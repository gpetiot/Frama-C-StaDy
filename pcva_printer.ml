
open Cil
open Cil_types
open Lexing
open Cil_datatype




let debug_builtins = Kernel.register_category "printer:builtins"
let print_var v =
  not (Cil.is_unused_builtin v) || Kernel.is_debug_key_enabled debug_builtins


let quantif_pred_cpt = ref 0
let quantif_pred_queue :
    ((Format.formatter -> unit) * (Format.formatter -> unit)) Queue.t =
  Queue.create ()
let postcond = ref None

(* How we handle \at terms (\at predicates are not supported) *)
let at_term_cpt = ref 0

let at_term_affect_in_function :
    ((Format.formatter -> unit) Queue.t) Datatype.String.Hashtbl.t =
  Datatype.String.Hashtbl.create 32

let no_repeat l =
  let rec aux acc = function
    | [] -> acc
    | h :: t when List.mem h acc -> aux acc t
    | h :: t -> aux (h :: acc) t
  in
  aux  [] l



(*
  first pass:
     - computes the output for \forall and \exists predicates
     - stores it somewhere
  second pass:
     - print the quantif-functions in the beginning of the file
     - print the function call where the predicate was used
*)
class pcva_printer ~first_pass () = object (self)
  inherit Printer.extensible_printer () as super

  val mutable current_function = None
  val mutable result_varinfo = None

  method private in_current_function vi =
    assert (current_function = None);
    current_function <- Some vi

  method private out_current_function =
    assert (current_function <> None);
    current_function <- None

  method private opt_funspec fmt funspec =
    if logic_printer_enabled && not (Cil.is_empty_funspec funspec) then
      Format.fprintf fmt "@[<hv 1>/*@@ %a@ */@]@\n" self#funspec funspec

  method private vdecl_complete fmt v =
    let display_ghost = v.vghost && not is_ghost in
    Format.fprintf fmt "@[<hov 0>%t%a;%t@]"
      (if display_ghost then fun fmt -> Format.fprintf fmt "/*@@ ghost@ "
       else ignore)
      self#vdecl v
      (if display_ghost then fun fmt -> Format.fprintf fmt "@ */" else ignore)


  (* to change a \valid to a pathcrawler_dimension *)
  (* term -> term * term *)
  method private extract_terms t =
    let loc = t.term_loc in
    match t.term_node with
    | TLval _ -> t, lzero ~loc ()
    | TCastE (_,term)
    | TCoerce (term,_)
    | TAlignOfE term -> self#extract_terms term
    | TBinOp (PlusPI,x,{term_node = Trange(_,Some y)})
    | TBinOp (IndexPI,x,{term_node = Trange(_,Some y)}) -> x,y
    | TBinOp (PlusPI,x,y)
    | TBinOp (IndexPI,x,y) -> x,y
    | TBinOp (MinusPI,x,y) ->
      x, term_of_exp_info loc (TUnOp(Neg,y)) {exp_type=t.term_type; exp_name=[]}
    | TStartOf _ -> t, lzero ~loc ()
    | TAddrOf (TVar _, TIndex _) ->
      let tnode = mkTermMem t TNoOffset in
      let term =
	term_of_exp_info loc (TLval tnode) {exp_type=t.term_type; exp_name=[]}
      in
      self#extract_terms term
    | _ ->
      failwith (Pretty_utils.sfprintf "unsupported term: %a" Printer.pp_term t)


  method private vars_of_term_lhost h =
    match h with
    | TVar lv -> (try [Extlib.the lv.lv_origin] with _ -> [])
    | TResult _ ->
      begin
	match result_varinfo with
	| None -> failwith "vars_of_term_lhost: no result_varinfo"
	| Some v -> [v]
      end
    | TMem t -> self#vars_of_term t

  method private vars_of_term_offset o =
    match o with
    | TNoOffset -> []
    | TField (_, t) -> self#vars_of_term_offset t
    | TModel _ -> []
    | TIndex (i,t) ->
      List.rev_append (self#vars_of_term i) (self#vars_of_term_offset t)

  method private vars_of_term_lval t =
    let h, o = t in
    List.rev_append (self#vars_of_term_lhost h) (self#vars_of_term_offset o)

  method private vars_of_term_node t =
    match t with
    | TLval tv
    | TAddrOf tv
    | TStartOf tv ->
      self#vars_of_term_lval tv
    | TSizeOfE t1
    | TAlignOfE t1
    | TUnOp(_,t1)
    | Tat(t1,_)
    | Tbase_addr(_,t1)
    | Toffset(_,t1)
    | Tblock_length(_,t1)
    | TLogic_coerce(_,t1)
    | TCoerce(t1,_)
    | Trange(None,Some t1)
    | Trange(Some t1,None)
    | TCastE(_,t1) -> self#vars_of_term t1
    | Trange (Some t1, Some t2)
    | TBinOp(_,t1,t2) ->
      List.rev_append (self#vars_of_term t1) (self#vars_of_term t2)
    | Tif(t1,t2,t3) ->
      List.rev_append (self#vars_of_term t1)
	(List.rev_append (self#vars_of_term t2) (self#vars_of_term t3))
    | _ -> []

  method private vars_of_term t =
    self#vars_of_term_node t.term_node

  method private vars_of_predicate p =
    match p with
    | Prel(_,t1,t2)
    | Pfresh(_,_,t1,t2) ->
      List.rev_append (self#vars_of_term t1) (self#vars_of_term t2)
    | Pvalid_read(_,t1)
    | Pvalid(_,t1)
    | Pinitialized(_,t1)
    | Pallocable(_,t1)
    | Pfreeable(_,t1) -> self#vars_of_term t1
    | Pand(p1,p2)
    | Por(p1,p2)
    | Pxor(p1,p2)
    | Pimplies(p1,p2)
    | Piff(p1,p2)
    | Pif(_,p1,p2) ->
      List.rev_append
	(self#vars_of_predicate_named p1)
	(self#vars_of_predicate_named p2)
    | Pnot(p1)
    | Pforall(_,p1)
    | Pexists(_,p1) -> self#vars_of_predicate_named p1
    | _ -> []

  method private vars_of_predicate_named p =
    self#vars_of_predicate p.content


  method term_node fmt t =
    let to_c_type = function
      | Ctype t -> t
      | Linteger -> longType
      | _ -> assert false in
    try
      match t.term_node with
      | Tat(_, StmtLabel _) -> failwith "\\at on stmt label unsupported!"
      | Tat(term,LogicLabel(_,stringlabel)) ->
	if stringlabel = "Old" then
	  if first_pass then
	    begin
	      let fct_name = try (Extlib.the current_function).vname
		with _ ->
		  failwith
		    (Pretty_utils.sfprintf
		       "no current function (term: %a)" Printer.pp_term t)
	      in
	      let affects = try
			      Datatype.String.Hashtbl.find
				at_term_affect_in_function fct_name
		with _ -> Queue.create() in
	      Queue.add (fun fmt ->
		Format.fprintf fmt "%a = %a;@\n"
		  (self#typ
		     (Some (fun fmt -> Format.fprintf fmt "term_at_%i"
		       !at_term_cpt)))
		  (to_c_type term.term_type)
		  self#term
		  term
	      ) affects;
	      Datatype.String.Hashtbl.add
		at_term_affect_in_function fct_name affects;
	    end
	  else
	    begin
	      Format.fprintf fmt "term_at_%i" !at_term_cpt;
	      at_term_cpt := !at_term_cpt + 1
	    end
	else
	  failwith (Printf.sprintf "\\at label '%s' unsupported!" stringlabel)
      | _ -> super#term_node fmt t
    with
      _ ->
	match t.term_node with
	| Tat(term,LogicLabel _) -> self#term fmt term
	| _ -> super#term_node fmt t
    

  method private predicate fmt pred =
    (* generate guards for logic vars, e.g.:
       [0 <= a <= 10; x <= b <= y] *)
    let rec aux acc vars p = 
      match p.content with
      | Pand({ content = Prel((Rlt | Rle) as r1, t11, t12) },
	     { content = Prel((Rlt | Rle) as r2, t21, t22) }) ->
	let rec terms t12 t21 = match t12.term_node, t21.term_node with
	  | TLval(TVar x1, TNoOffset), TLval(TVar x2, TNoOffset) -> 
	    let v, vars = match vars with
	      | [] -> assert false
	      | v :: tl -> 
		match v.lv_type with
		| Ctype ty when isIntegralType ty -> v, tl
		| Linteger -> v, tl
		| Ltype _ as ty when Logic_const.is_boolean_type ty ->
		  v, tl
		| Ctype _ | Ltype _ | Lvar _ | Lreal | Larrow _ -> 
		  assert false
	    in
	    if Logic_var.equal x1 x2 && Logic_var.equal x1 v then
	      (t11, r1, x1, r2, t22) :: acc, vars
	    else
	      assert false
	  | TLogic_coerce(_, t12), _ -> terms t12 t21 
	  | _, TLogic_coerce(_, t21) -> terms t12 t21
	  | TLval _, _ -> assert false
	  | _, _ -> assert false
	in
	terms t12 t21
      | Pand(p1, p2) -> 
	let acc, vars = aux acc vars p1 in
	aux acc vars p2
      | _ -> assert false
    in
    match pred with
    | Ptrue -> Format.fprintf fmt "1"
    | Pfalse -> Format.fprintf fmt "0"
    | Pvalid(_,term)
    | Pvalid_read(_,term) ->
      let x, y = self#extract_terms term in
      Format.fprintf fmt "((%a) >= 0 && (pathcrawler_dimension(%a) > (%a)))"
	self#term y self#term x self#term y
    | Pforall(logic_vars,pred) ->
      begin
	if (List.length logic_vars) > 1 then
	  failwith "\\forall quantification on many variables unsupported!";
	match pred.content with
	| Pimplies(hyps,goal) ->

	  
	  if first_pass then
	    let guards, vars = aux [] logic_vars hyps in
	    if vars <> [] then
	      failwith "Unguarded variables in \\forall !"
	    else
	      let t1,r1,lv,r2,t2 = List.hd guards in
	      let vars = self#vars_of_predicate_named pred in (* pour l'appel *)
	      let vars = no_repeat vars in
	      let logic_var = List.hd logic_vars in
	      let vars = List.filter
		(fun v -> v.vname <> logic_var.lv_name) vars in
	      let to_c_type = function
		| Ctype t -> t
		| Linteger -> longType
		| _ -> assert false in
	      let args = List.map (fun v -> v.vname) vars in
	      let args = List.fold_left (fun x y -> x^","^y) "" args in
	      let args = String.sub args 1 ((String.length args)-1) in
	      let typed_args = List.map (fun v ->
		Format.fprintf
		  Format.str_formatter "%a"
		  (self#typ
		     (Some (fun fmt ->
		       Format.fprintf fmt "%s" v.vname)))
		  v.vtype;
		Format.flush_str_formatter()
	      ) vars in
	      let typed_args =
		List.fold_left (fun x y -> x^","^y) "" typed_args in
	      let typed_args =
		String.sub typed_args 1 ((String.length typed_args)-1) in
	      let fct_forall fmt =
		Format.fprintf fmt
		  "int forall_%i (%s) {\n  %a %s = %a%s;\n  while(%s %a %a) {\n    if(!(%a))\n      return 0;\n    %s ++;\n  }\n  return 1;\n}\n\n"
		  !quantif_pred_cpt typed_args (self#typ None)
		  (to_c_type lv.lv_type) lv.lv_name self#term t1
		  (match r1 with Rlt -> "+1" | Rle -> "" | _ -> assert false)
		  lv.lv_name self#relation r2 self#term t2
		  self#predicate_named goal lv.lv_name
	      in
	      let call_forall fmt =
		Format.fprintf fmt
		  "(forall_%i(%s))"
		  !quantif_pred_cpt args
	      in
	      (* the ref quantif_pred_cpt has to be incremented before each
		 printing of these functions *)
	      Queue.add (fct_forall, call_forall) quantif_pred_queue
	  else
	    begin
	      let _,call_forall = Queue.take quantif_pred_queue in
	      call_forall fmt;
	      quantif_pred_cpt := !quantif_pred_cpt + 1
	    end

	  

	| _ -> failwith "\\forall not of the form \\forall ...; a ==> b;"
      end
    | Pexists(logic_vars,pred) ->
       begin
	if (List.length logic_vars) > 1 then
	  failwith "\\exists quantification on many variables unsupported!";
	match pred.content with
	| Pand(hyps,goal) ->

	  
	  if first_pass then
	    let guards, vars = aux [] logic_vars hyps in
	    if vars <> [] then
	      failwith "Unguarded variables in \\exists !"
	    else
	      let t1,r1,lv,r2,t2 = List.hd guards in
	      let vars = self#vars_of_predicate_named pred in (* pour l'appel *)
	      let vars = no_repeat vars in
	      let logic_var = List.hd logic_vars in
	      let vars = List.filter
		(fun v -> v.vname <> logic_var.lv_name) vars in
	      let to_c_type = function
		| Ctype t -> t
		| Linteger -> longType
		| _ -> assert false in
	      let args = List.map (fun v -> v.vname) vars in
	      let args = List.fold_left (fun x y -> x^","^y) "" args in
	      let args = String.sub args 1 ((String.length args)-1) in
	      let typed_args = List.map (fun v ->
		Format.fprintf
		  Format.str_formatter "%a"
		  (self#typ
		     (Some (fun fmt ->
		       Format.fprintf fmt "%s" v.vname)))
		  v.vtype;
		Format.flush_str_formatter()
	      ) vars in
	      let typed_args =
		List.fold_left (fun x y -> x^","^y) "" typed_args in
	      let typed_args =
		String.sub typed_args 1 ((String.length typed_args)-1) in
	      let fct_exists fmt =
		Format.fprintf fmt
		  "int exists_%i (%s) {\n  %a %s = %a%s;\n  while(%s %a %a) {\n    if(%a)\n      return 1;\n    %s ++;\n  }\n  return 0;\n}\n\n"
		  !quantif_pred_cpt typed_args (self#typ None)
		  (to_c_type lv.lv_type) lv.lv_name self#term t1
		  (match r1 with Rlt -> "+1" | Rle -> "" | _ -> assert false)
		  lv.lv_name self#relation r2 self#term t2
		  self#predicate_named goal lv.lv_name
	      in
	      let call_exists fmt =
		Format.fprintf fmt
		  "(exists_%i(%s))"
		  !quantif_pred_cpt args
	      in
	      (* the ref quantif_pred_cpt has to be incremented before each
		 printing of these functions *)
	      Queue.add (fct_exists, call_exists) quantif_pred_queue
	  else
	    begin
	      let _,call_exists = Queue.take quantif_pred_queue in
	      call_exists fmt;
	      quantif_pred_cpt := !quantif_pred_cpt + 1
	    end

	  

	| _ -> failwith "\\exists not of the form \\exists ...; a && b;"
      end
    | Pimplies(pred1,pred2) ->
      Format.fprintf fmt "(!(%a) || %a)"
	self#predicate_named pred1
	self#predicate_named pred2
    | Piff(pred1,pred2) ->
      Format.fprintf fmt "( ( !(%a) || %a ) && ( !(%a) || %a ) )"
	self#predicate_named pred1
	self#predicate_named pred2
	self#predicate_named pred2
	self#predicate_named pred1
    | Pat _ -> failwith "\\at on predicates unsupported!"
    | Pseparated _ ->
      begin
	Options.Self.feedback "Predicate ignored: %a" Printer.pp_predicate pred;
	Format.fprintf fmt "1"
      end
    | _ -> super#predicate fmt pred

  method private predicate_named fmt pred_named =
    self#predicate fmt pred_named.content

      

  method private annotated_stmt next fmt stmt =
    self#stmt_labels fmt stmt;
    let kf = Kernel_function.find_englobing_kf stmt in
    let begin_loop = ref [] in
    let end_loop = ref [] in
    let has_code_annots = List.length (Annotations.code_annot stmt) > 0 in
    if has_code_annots then
      Format.fprintf fmt "{@[<h 2>@\n";
    Annotations.iter_code_annot (fun _emitter ca ->
      let prop = Property.ip_of_code_annot_single kf stmt ca in
      let id = Prop_id.to_id prop in
      let ca = ca.annot_content in
      let behaviors =
	match ca with
	| AAssert (b,_)
	| AStmtSpec (b,_)
	| AInvariant (b,_,_) -> b
	| _ -> []
      in
      let behaviors =
	List.map (fun bname ->
	  let ret = ref [] in
	  Annotations.iter_behaviors (fun _emit beh ->
	    if beh.b_name = bname then
	      ret := beh.b_assumes
	  ) kf;
	  !ret
	) behaviors
      in
      let pc_assert_exception fmt pred msg id =
	Format.fprintf fmt
	  "@[<v 2>if(!(%a)) pathcrawler_assert_exception(\"%s\", %i);@]@\n"
	  self#predicate_named pred msg id
      in
      match ca with
      | AAssert (_,pred) ->
	if behaviors = [] then
	  pc_assert_exception fmt pred "Assert!" id
	else
	  begin
	    Format.fprintf fmt "@[<v 2>if (";
	    List.iter (fun assumes ->
	      Format.fprintf fmt "(";
	      List.iter (fun a ->
		Format.fprintf fmt "%a &&" self#predicate a.ip_content
	      ) assumes;
	      Format.fprintf fmt " 1 ) || "
	    ) behaviors;
	    Format.fprintf fmt " 0 )@]";
	    pc_assert_exception fmt pred "Assert!" id
	  end
      | AInvariant (_,true,pred) ->
	if behaviors = [] then
	  begin
	    pc_assert_exception fmt pred "Loop invariant not established!" id;
	    end_loop :=
	      (fun fmt ->
		pc_assert_exception fmt pred
		  "Loop invariant not preserved!" id)
	    :: !end_loop
	  end
	else
	  begin
	    Format.fprintf fmt "@[<v 2>if (";
	    List.iter (fun assumes ->
	      Format.fprintf fmt "(";
	      List.iter (fun a ->
		Format.fprintf fmt "%a &&" self#predicate a.ip_content
	      ) assumes;
	      Format.fprintf fmt " 1 ) || "
	    ) behaviors;
	    Format.fprintf fmt " 0 )@]";
	    pc_assert_exception fmt pred "Loop invariant not established!" id;
	    end_loop :=
	      (fun fmt ->
		Format.fprintf fmt "@[<v 2>if (";
		List.iter (fun assumes ->
		  Format.fprintf fmt "(";
		  List.iter (fun a ->
		    Format.fprintf fmt "%a &&" self#predicate a.ip_content
		  ) assumes;
		  Format.fprintf fmt " 1 ) || "
		) behaviors;
		Format.fprintf fmt " 0 )@]";
		pc_assert_exception fmt pred "Loop invariant not preserved!" id)
	    :: !end_loop
	  end
      | AVariant (term,_) ->
	Format.fprintf fmt
	  "@[<v 2>if((%a)<0) pathcrawler_assert_exception(\"%s\",%i);@]@\n"
	  self#term term "Variant non positive!" id;
	begin_loop :=
	  (fun fmt ->
	    Format.fprintf fmt "int old_variant_%i = %a;\n" id self#term term)
	:: !begin_loop;
	end_loop :=
	  (fun fmt ->
	    Format.fprintf fmt
	      "@[<v 2>if((%a) >= old_variant_%i) pathcrawler_assert_exception(\"%s\",%i);@]@\n"
	      self#term term id "Variant non decreasing!" id)
	:: !end_loop
      | _ -> ()
    ) stmt;

    begin
      match stmt.skind with
      | Loop(_,b,l,_,_) ->
	Format.fprintf fmt "%a@[<v 2>while (1) {@\n"
	  (fun fmt -> self#line_directive fmt) l;
	List.iter (fun s -> s fmt) !begin_loop;
	Format.fprintf fmt "%a" (fun fmt -> self#block fmt) b;
	List.iter (fun s -> s fmt) !end_loop;
	Format.fprintf fmt "}@\n @]"
      | Return _ ->
	begin
	  match !postcond with
	  | Some post_cond ->
	    begin
	      post_cond fmt;
	      postcond := None;
	      self#stmtkind next fmt stmt.skind
	    end
	  | None -> self#stmtkind next fmt stmt.skind
	end
      | _ -> self#stmtkind next fmt stmt.skind
    end;
    if has_code_annots then
      Format.fprintf fmt "@]@\n}"



  method private compute_result_varinfo f =
    List.iter (fun stmt ->
      match stmt.skind with
      | Return(Some {enode = Lval(Var v,_)},_) ->
	result_varinfo <- Some v
      | _ -> ()
    ) f.sallstmts


  method private fundecl fmt f =
    (* declaration. *)
    let was_ghost = is_ghost in
    let entry_point_name =
      Kernel_function.get_name (fst(Globals.entry_point())) in
    let kf = Globals.Functions.find_by_name f.svar.vname in
    let behaviors = Annotations.behaviors kf in
    let pc_assert_exception fmt pred msg id =
      Format.fprintf fmt
	"@[<v 2>if(!(%a)) pathcrawler_assert_exception(\"%s\", %i);@]@\n"
	self#predicate pred msg id
    in
    let entering_ghost = f.svar.vghost && not was_ghost in
    self#compute_result_varinfo f;

    (* BEGIN precond (entry-point) *)
    if f.svar.vname = entry_point_name then
      begin
	let x,y,z =
	  match f.svar.vtype with
	  | TFun(_,x,y,z) -> x,y,z
	  | _ -> assert false
	in
	Format.fprintf fmt "%a {@[<v 2>@\n"
	  (self#typ
	     (Some (fun fmt ->
	       Format.fprintf fmt "%s_precond" entry_point_name)))
	  (TFun(intType,x,y,z));
	List.iter (fun b ->
	  let assumes = b.b_assumes in
	  let requires = b.b_requires in
	  let assumes fmt =
	    if assumes <> [] then
	      begin
		Format.fprintf fmt "@[<v 2>if (";
		List.iter (fun a ->
		  Format.fprintf fmt "%a &&" self#predicate a.ip_content
		) assumes;
		Format.fprintf fmt " 1 )"
	      end
	  in
	  List.iter (fun pred ->
	    assumes fmt;
	    Format.fprintf fmt
	      "{@\n@[<v 2>if(!(%a)) return 0;@]@]@\n}"
	      self#predicate pred.ip_content
	  ) requires
	) behaviors;
	Format.fprintf fmt "return 1;@\n@]}@\n@\n"
      end;
    (* END precond (entry-point) *)




    Format.fprintf fmt "@[%t%a@\n@[<v 2>"
      (if entering_ghost then fun fmt -> Format.fprintf fmt "/*@@ ghost@ " 
       else ignore)
      self#vdecl f.svar;
    (* body. *)
    if entering_ghost then is_ghost <- true;
    
    Format.fprintf fmt "@[<h 2>{@\n";
    (* BEGIN precond (not entry-point) *)
    if f.svar.vname <> entry_point_name then
      begin
	List.iter (fun b ->
	  let assumes = b.b_assumes in
	  let requires = b.b_requires in
	  let assumes fmt =
	    if assumes <> [] then
	      begin
		Format.fprintf fmt "@[<v 2>if (";
		List.iter (fun a ->
		  Format.fprintf fmt "%a &&" self#predicate a.ip_content
		) assumes;
		Format.fprintf fmt " 1 )"
	      end
	  in
	  List.iter (fun pred ->
	    let prop = Property.ip_of_requires kf Kglobal b pred in
	    let id = Prop_id.to_id prop in
	    assumes fmt;
	    pc_assert_exception fmt pred.ip_content "Pre-condition!" id;
	    Format.fprintf fmt "@]"
	  ) requires
	) behaviors
      end;
    (* END precond (not entry-point) *)

    
    (* BEGIN postcond *)
    postcond :=
      if List.length behaviors > 0 then
	Some (fun fmt ->
	  Format.fprintf fmt "@[<h 2>{@\n";
	  List.iter (fun b ->
	    let assumes = b.b_assumes in
	    let ensures = b.b_post_cond in
	    let assumes fmt =
	      if assumes <> [] then
		begin
		  Format.fprintf fmt "@[<v 2>if (";
		  List.iter (fun a ->
		    Format.fprintf fmt "%a &&" self#predicate a.ip_content
		  ) assumes;
		  Format.fprintf fmt " 1 )"
		end
	    in
	    List.iter (fun (tk,pred) ->
	      let prop = Property.ip_of_ensures kf Kglobal b (tk,pred) in
	      let id = Prop_id.to_id prop in
	      assumes fmt;
	      pc_assert_exception fmt pred.ip_content "Post-condition!" id;
	      Format.fprintf fmt "@]"
	    ) ensures
	  ) behaviors;
	  Format.fprintf fmt "@]@\n}@\n"
	)
      else
	None;
    (* END postcond *)


    (* variables for \at terms *)
    begin
      if not first_pass then
	begin
	  try
	    let q =
	      Datatype.String.Hashtbl.find
		at_term_affect_in_function f.svar.vname
	    in
	    let tmp = !at_term_cpt in
	    Queue.iter (fun e -> e fmt; at_term_cpt := !at_term_cpt + 1) q;
	    at_term_cpt := tmp
	  with _ -> ()
	end
    end;
    
    self#block ~braces:true fmt f.sbody;
    begin
      match !postcond with
      | Some post_cond -> post_cond fmt; postcond := None
      | None -> ()
    end;
    Format.fprintf fmt "@.}";
    
    if entering_ghost then is_ghost <- false;
    Format.fprintf fmt "@]%t@]@."
      (if entering_ghost then fun fmt -> Format.fprintf fmt "@ */" else ignore)


  method global fmt (g:global) =
    match g with
    | GFun (fundec, l) ->
      if print_var fundec.svar
      then begin
	self#in_current_function fundec.svar;
	(* If the function has attributes then print a prototype because
	 * GCC cannot accept function attributes in a definition *)
	let oldattr = fundec.svar.vattr in
	(* Always pring the file name before function declarations *)
	(* Prototype first *)
	if oldattr <> [] then
	  (self#line_directive fmt l;
	   Format.fprintf fmt "%a;@\n"
	     self#vdecl_complete fundec.svar);
	(* Temporarily remove the function attributes *)
	fundec.svar.vattr <- [];
	(* Body now *)
	self#line_directive ~forcefile:true fmt l;
	self#fundecl fmt fundec;
	fundec.svar.vattr <- oldattr;
	Format.fprintf fmt "@\n";
	self#out_current_function
      end

    | GType (typ, l) ->
      self#line_directive ~forcefile:true fmt l;
      Format.fprintf fmt "typedef %a;@\n"
	(self#typ (Some (fun fmt -> Format.fprintf fmt "%s" typ.tname)))
	typ.ttype

    | GEnumTag (enum, l) ->
      self#line_directive fmt l;
      if verbose then 
        Format.fprintf fmt "/* Following enum is equivalent to %a */@\n" 
          (self#typ None) 
          (TInt(enum.ekind,[]));
      Format.fprintf fmt "enum@[ %a {@\n%a@]@\n}%a;@\n"
	self#varname enum.ename
	(Pretty_utils.pp_list ~sep:",@\n"
	   (fun fmt item ->
	     Format.fprintf fmt "%s = %a"
	       item.einame
	       self#exp item.eival))
	enum.eitems
	self#attributes enum.eattr

    | GEnumTagDecl (enum, l) -> (* This is a declaration of a tag *)
      self#line_directive fmt l;
      Format.fprintf fmt "enum %a;@\n" self#varname enum.ename

    | GCompTag (comp, l) -> (* This is a definition of a tag *)
      let n = comp.cname in
      let su =
	if comp.cstruct then "struct"
	else "union"
      in
      let sto_mod, rest_attr = Cil.separateStorageModifiers comp.cattr in
      self#line_directive ~forcefile:true fmt l;
      Format.fprintf fmt "@[<3>%s%a %a {@\n%a@]@\n}%a;@\n"
	su
	self#attributes sto_mod
	self#varname n
	(Pretty_utils.pp_list ~sep:"@\n" self#fieldinfo)
	comp.cfields
	self#attributes rest_attr

    | GCompTagDecl (comp, l) -> (* This is a declaration of a tag *)
      self#line_directive fmt l;
      Format.fprintf fmt "%s;@\n" (Cil.compFullName comp)

    | GVar (vi, io, l) ->
      if print_var vi then begin
	self#line_directive ~forcefile:true fmt l;
        if vi.vghost then Format.fprintf fmt "/*@@ ghost@ ";
	self#vdecl fmt vi;
	(match io.init with
	  None -> ()
	| Some i ->
	  Format.fprintf fmt " = ";
	  let islong =
	    match i with
	      CompoundInit (_, il) when List.length il >= 8 -> true
	    | _ -> false
	  in
	  if islong then begin
	    self#line_directive fmt l;
	    Format.fprintf fmt "  @[@\n"
	  end;
	  self#init fmt i;
	  if islong then Format.fprintf fmt "@]");
	Format.fprintf fmt ";%t@\n" 
          (if vi.vghost then fun fmt -> Format.fprintf fmt "@ */" else ignore)
      end
    (* print global variable 'extern' declarations, and function prototypes *)
    | GVarDecl (funspec, vi, l) ->
      if print_var vi then begin
	if Cil.isFunctionType vi.vtype then self#in_current_function vi;
	self#opt_funspec fmt funspec;
	begin
	  self#line_directive fmt l;
	  Format.fprintf fmt "%a@\n@\n" self#vdecl_complete vi
	end;
	if Cil.isFunctionType vi.vtype then self#out_current_function
      end

    | GAsm (s, l) ->
      self#line_directive fmt l;
      Format.fprintf fmt "__asm__(\"%s\");@\n" (Escape.escape_string s)

    | GPragma (Attr(_an, _args), _l) -> Format.fprintf fmt "@\n"

    | GPragma (AttrAnnot _, _) -> Format.fprintf fmt "@\n"

    | GAnnot (decl,l) ->
      self#line_directive fmt l;
      Format.fprintf fmt "/*@@@ %a@ */@\n"
	self#global_annotation decl

    | GText s  ->
      if s <> "//" then
	Format.fprintf fmt "%s@\n" s


  method file fmt f =
    Queue.iter (fun (a,_) ->
      a fmt;
      quantif_pred_cpt := !quantif_pred_cpt + 1;
    ) quantif_pred_queue;
    quantif_pred_cpt := 0;
    super#file fmt f

  method term_lval fmt t =
    match t with
    | (TResult _,_) ->
      begin
	match result_varinfo with
	| None -> failwith "term_lval: no result_varinfo"
	| Some v -> Format.fprintf fmt "%s" v.vname
      end
    | _ -> super#term_lval fmt t
end


module First_pass =
  Printer_builder.Make
    (struct class printer = pcva_printer ~first_pass:true end)

module Second_pass =
  Printer_builder.Make
    (struct class printer = pcva_printer ~first_pass:false end)
 

