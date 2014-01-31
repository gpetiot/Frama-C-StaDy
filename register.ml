
open Cil_types
open Lexing



let print_strtbl_vartbl_terms hashtbl dkey =
  Options.Self.debug ~dkey "========================";
  Datatype.String.Hashtbl.iter_sorted (fun f tbl ->
    Options.Self.debug ~dkey "function '%s'" f;
    Cil_datatype.Varinfo.Hashtbl.iter_sorted (fun v ts ->
      Options.Self.debug ~dkey "var '%s'" v.vname;
      List.iter (fun t -> Options.Self.debug ~dkey "%a " Printer.pp_term t) ts
    ) tbl;
    Options.Self.debug ~dkey "----------------"
  ) hashtbl;
  Options.Self.debug ~dkey "========================"




(* Appends an element to the end of a list. *)
let append_end : 'a list -> 'a -> 'a list =
  fun l elt -> List.rev_append (List.rev l) [elt]





(* Extracts the varinfo of the variable and its inferred size as a term
   from a term t as \valid(t). *)
let rec extract_from_valid : term -> varinfo * term =
  fun t -> match t.term_node with
  | TBinOp((PlusPI|IndexPI),
	   ({term_node=TLval(TVar v, _)} as _t1),
	   ({term_node=Trange(_,Some bound)} as _t2)) ->
    let varinfo = Extlib.the v.lv_origin in
    let tnode = TBinOp (PlusA, bound, Cil.lone ~loc:t.term_loc()) in
    let einfo = {exp_type=bound.term_type; exp_name=[]} in
    let term = Cil.term_of_exp_info t.term_loc tnode einfo in
    varinfo, term

  | TBinOp((PlusPI|IndexPI),
	   ({term_node=TLval(TVar v, _)} as _t1),
	   (t2 (* anything but a Trange *))) ->
    let varinfo = Extlib.the v.lv_origin in
    let tnode = TBinOp (PlusA, t2, Cil.lone ~loc:t.term_loc()) in
    let einfo = {exp_type=t2.term_type; exp_name=[]} in
    let term = Cil.term_of_exp_info t.term_loc tnode einfo in
    varinfo, term

  | TBinOp((PlusPI|IndexPI),
	   ({term_node=TLval tlval}),
	   ({term_node=Trange(_,Some bound)})) ->
    let tnode = TBinOp (PlusA, bound, Cil.lone ~loc:t.term_loc()) in
    let einfo = {exp_type=bound.term_type; exp_name=[]} in
    let term = Cil.term_of_exp_info t.term_loc tnode einfo in
    let varinfo, _ = extract_from_valid {t with term_node=TLval tlval} in
    varinfo, term
    
    

  | TLval (TVar v, TNoOffset) ->
    let varinfo = Extlib.the v.lv_origin in
    let term = Cil.lone ~loc:t.term_loc () in
    varinfo, term
  | TLval (TVar _, TField _) -> assert false
  | TLval (TVar _, TModel _) -> assert false
  | TLval (TVar _, TIndex _) -> assert false
  

  | TLval (TMem m, TNoOffset) ->
    let varinfo, _ = extract_from_valid m in
    let term = Cil.lone ~loc:t.term_loc () in
    varinfo, term
  | TLval (TMem _, TField _) -> assert false
  | TLval (TMem _, TModel _) -> assert false
  | TLval (TMem _, TIndex _) -> assert false


  | TStartOf _ -> Options.Self.debug ~dkey:Options.dkey_lengths
    "TStartOf \\valid(%a) ignored" Printer.pp_term t;
    assert false
  | TAddrOf _ -> Options.Self.debug ~dkey:Options.dkey_lengths
    "TAddrOf \\valid(%a) ignored" Printer.pp_term t;
    assert false
  | TCoerce _ -> Options.Self.debug ~dkey:Options.dkey_lengths
    "TCoerce \\valid(%a) ignored" Printer.pp_term t;
    assert false
  | TCoerceE _ -> Options.Self.debug ~dkey:Options.dkey_lengths
    "TCoerceE \\valid(%a) ignored" Printer.pp_term t;
    assert false
  | TLogic_coerce _ -> Options.Self.debug ~dkey:Options.dkey_lengths
    "TLogic_coerce \\valid(%a) ignored" Printer.pp_term t;
    assert false
  | TBinOp _ -> Options.Self.debug ~dkey:Options.dkey_lengths
    "TBinOp \\valid(%a) ignored" Printer.pp_term t;
    assert false
  | _ -> Options.Self.debug ~dkey:Options.dkey_lengths
    "\\valid(%a) ignored" Printer.pp_term t;
    assert false



(* Computes and returns a hashtable such that :
   function_name1 =>
   -  var1 => inferred size for var1
   -  var2 => inferred size for var2
   function_name2 =>
   -  ...
*)
let lengths_from_requires :
    unit
    -> term list Cil_datatype.Varinfo.Hashtbl.t Datatype.String.Hashtbl.t =
  fun () ->
    let lengths = Datatype.String.Hashtbl.create 32 in
    Globals.Functions.iter (fun kf ->
      let vi = Kernel_function.get_vi kf in
      if not (Cil.is_unused_builtin vi) then
	begin
	  let kf_name = Kernel_function.get_name kf in
	  let kf_tbl = Cil_datatype.Varinfo.Hashtbl.create 32 in

	  Annotations.iter_behaviors (fun _ bhv ->
	    List.iter (fun id_pred ->
	      let pred = id_pred.ip_content in
	      let c = new Sd_subst.subst in
	      let pred = c#subst_pred pred [] [] [] in

	      let o = object
		inherit Visitor.frama_c_inplace

		method! vpredicate p =
		  match p with
		  | Pvalid(_, t) | Pvalid_read(_, t) ->
		    begin
		      (*try*)
			let varinfo, term = extract_from_valid t in
			let terms =
			  try Cil_datatype.Varinfo.Hashtbl.find kf_tbl varinfo
			  with Not_found -> []
			in
			let terms = append_end terms term in
			Cil_datatype.Varinfo.Hashtbl.replace
			  kf_tbl varinfo terms;
			Cil.DoChildren
		      (*with
		      | _ -> Cil.DoChildren*)
		    end
		  | _ -> Cil.DoChildren
	      end
	      in
	      
	      ignore (Visitor.visitFramacPredicate o pred)
	    ) bhv.b_requires
	  ) kf;
	  Datatype.String.Hashtbl.add lengths kf_name kf_tbl
	end
    );
    Options.Self.debug ~dkey:Options.dkey_lengths "LENGTHS:";
    print_strtbl_vartbl_terms lengths Options.dkey_lengths;
    lengths





(* Computes and returns a hashtable such that :
   function_name1 =>
   -  formal var1 => size of var1 saved
   -  formal var2 => size of var2 saved
   function_name2 =>
   -  ...
*)
let at_from_formals :
    term list Cil_datatype.Varinfo.Hashtbl.t Datatype.String.Hashtbl.t
    -> term list Cil_datatype.Varinfo.Hashtbl.t Datatype.String.Hashtbl.t =
  fun lengths ->
    let terms_at_Pre = Datatype.String.Hashtbl.create 32 in
    Globals.Functions.iter (fun kf ->
      let vi = Kernel_function.get_vi kf in
      if not (Cil.is_unused_builtin vi) then
	begin
	  let kf_name = Kernel_function.get_name kf in
	  let kf_tbl = Cil_datatype.Varinfo.Hashtbl.create 32 in
	  let lengths_tbl = Datatype.String.Hashtbl.find lengths kf_name in
	  let formals = Kernel_function.get_formals kf in
	  List.iter (fun vi ->
	    let terms =
	      try Cil_datatype.Varinfo.Hashtbl.find lengths_tbl vi
	      with Not_found -> []
	    in
	    Cil_datatype.Varinfo.Hashtbl.add kf_tbl vi terms
	  ) formals;
	  Datatype.String.Hashtbl.add terms_at_Pre kf_name kf_tbl
	end
    );
    Options.Self.debug ~dkey:Options.dkey_at "AT:";
    print_strtbl_vartbl_terms terms_at_Pre Options.dkey_at;
    terms_at_Pre







let debug_builtins = Kernel.register_category "printer:builtins"

let print_var v =
  not (Cil.is_unused_builtin v) || Kernel.is_debug_key_enabled debug_builtins

let no_repeat : 'a list -> 'a list =
  fun l ->
    let rec aux acc = function
      | [] -> acc
      | h :: t when List.mem h acc -> aux acc t
      | h :: t -> aux (h :: acc) t
    in
    aux  [] l

(* to change a \valid to a pathcrawler_dimension *)
let rec extract_terms : term -> term * term =
  fun t ->
    let loc = t.term_loc in
    match t.term_node with
    | TLval _ -> t, Cil.lzero ~loc ()
    | TCastE (_,term)
    | TCoerce (term,_)
    | TAlignOfE term -> extract_terms term
    | TBinOp ((PlusPI|IndexPI),x,{term_node = Trange(_,Some y)}) -> x,y
    | TBinOp ((PlusPI|IndexPI),x,y) -> x,y
    | TBinOp (MinusPI,x,y) ->
      let einfo = {exp_type=t.term_type; exp_name=[]} in
      x, Cil.term_of_exp_info loc (TUnOp(Neg,y)) einfo
    | TStartOf _ -> t, Cil.lzero ~loc ()
    | TAddrOf (TVar _, TIndex _) ->
      let lv = Cil.mkTermMem t TNoOffset in
      let einfo = {exp_type=t.term_type;exp_name=[]} in
      let te = Cil.term_of_exp_info loc(TLval lv) einfo in
      extract_terms te
    | _ -> Options.Self.not_yet_implemented "term: %a" Printer.pp_term t




(* generate guards for logic vars, e.g.:
   [0 <= a <= 10; x <= b <= y]
   TODO: what is the 2nd value of the returned tuple (logic_var list) ???
*)
let rec compute_guards
    : (term*relation*logic_var*relation*term)list ->
  logic_var list ->
  predicate named ->
  ((term*relation*logic_var*relation*term)list * logic_var list) =
  fun acc vars p ->
    match p.content with
    | Pand({ content = Prel((Rlt | Rle) as r1, t11, t12) },
	   { content = Prel((Rlt | Rle) as r2, t21, t22) }) ->
      let rec terms t12 t21 = match t12.term_node, t21.term_node with
	| TLval(TVar x1, TNoOffset), TLval(TVar x2, TNoOffset) -> 
	  let v, vars = match vars with
	    | [] -> assert false
	    | v :: tl -> 
	      match v.lv_type with
	      | Ctype ty when Cil.isIntegralType ty -> v, tl
	      | Linteger -> v, tl
	      | Ltype _ as ty when Logic_const.is_boolean_type ty -> v, tl
	      | Ctype _ | Ltype _ | Lvar _ | Lreal | Larrow _ -> assert false
	  in
	  if Cil_datatype.Logic_var.equal x1 x2
	    && Cil_datatype.Logic_var.equal x1 v then
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
      let acc, vars = compute_guards acc vars p1 in
      compute_guards acc vars p2
    | _ ->
      Options.Self.feedback "compute_guards of %a" Printer.pp_predicate_named p;
      assert false









class sd_printer props terms_at_Pre () = object(self)
  inherit Printer.extensible_printer () as super

  val mutable pred_cpt = 0
  val mutable postcond = None
  val mutable dealloc = None
  val mutable result_varinfo = None
  val mutable current_function = None
  val mutable in_old_term = false
  val mutable in_old_ptr = false
  val mutable first_global = true
    
  (* unmodified *)  
  method private in_current_function vi =
    assert (current_function = None);
    current_function <- Some vi

  (* unmodified *)
  method private out_current_function =
    assert (current_function <> None);
    current_function <- None

  (* unmodified *)
  method private opt_funspec fmt funspec =
    if logic_printer_enabled && not (Cil.is_empty_funspec funspec) then
      Format.fprintf fmt "@[<hv 1>/*@@ %a@ */@]@\n" self#funspec funspec

  (* unmodified *)
  method private vdecl_complete fmt v =
    let display_ghost = v.vghost && not is_ghost in
    Format.fprintf fmt "@[<hov 0>%t%a;%t@]"
      (if display_ghost then fun fmt -> Format.fprintf fmt "/*@@ ghost@ "
       else ignore)
      self#vdecl v
      (if display_ghost then fun fmt -> Format.fprintf fmt "@ */" else ignore)

  (* replace a varinfo by old_varinfo, according to the terms_at_Pre hashtbl *)
  method! varinfo fmt v =
    if in_old_term then
      match current_function with
      | Some f ->
	begin
	  let prefix =
	    if Cil.isPointerType v.vtype && in_old_ptr then "old_ptr" else "old"
	  in
	  try
	    let tbl = Datatype.String.Hashtbl.find terms_at_Pre f.vname in
	    ignore (Cil_datatype.Varinfo.Hashtbl.find tbl v);
	    super#varinfo fmt {v with vname=prefix^"_"^v.vname}
	  with
	  | Not_found ->
	    Options.Self.feedback ~dkey:Options.dkey_at
	      "%s_%s not found in terms_at_Pre" prefix v.vname;
	    super#varinfo fmt v
	end
      | None -> super#varinfo fmt v
    else
      super#varinfo fmt v

  method! logic_var fmt v =
    if in_old_term then
      match current_function with
      | Some f ->
	begin
	  let prefix =
	    match v.lv_type with Ctype ty ->
	      if Cil.isPointerType ty && in_old_ptr then "old_ptr" else "old"
	    | _ -> "old"
	  in
	  try
	    let tbl = Datatype.String.Hashtbl.find terms_at_Pre f.vname in
	    let vi = Extlib.the v.lv_origin in
	    ignore (Cil_datatype.Varinfo.Hashtbl.find tbl vi);
	    super#logic_var fmt {v with lv_name=prefix^"_"^v.lv_name}
	  with
	  | _ ->
	    Options.Self.feedback ~dkey:Options.dkey_at
	      "%s_%s not found in terms_at_Pre" prefix v.lv_name;
	    super#logic_var fmt v
	end
      | None -> super#logic_var fmt v
    else
      super#logic_var fmt v

  (* support of the litteral value of INT_MIN *)
  method! exp fmt e =
    match e.enode with
    | UnOp(Neg,{enode=Const(CInt64 (_,_,str))},_) ->
      begin
	match str with
	| Some s when s = "2147483648" -> Format.fprintf fmt "(-2147483467-1)"
	| _ -> super#exp fmt e
      end
    | _ -> super#exp fmt e

  (* unmodified *)
  method! term fmt t = self#term_node fmt t

  (* special treatment for \old terms *)
  method! term_node fmt t =
    match t.term_node with
    | TConst(Integer(i,_)) ->
      if (Integer.to_string i) = "-2147483648" then
	Format.fprintf fmt "(-2147483647-1)"
      else
	super#term_node fmt t
    | Tat(_, StmtLabel _) ->
      if current_function <> None then
	Options.Self.warning "%a unsupported" Printer.pp_term t;
      super#term_node fmt t
    | Tat(term,LogicLabel(_,stringlabel)) ->
      if stringlabel = "Old" || stringlabel = "Pre" then
	begin
	  let is_ptr =
	    match term.term_node with TLval(TMem _,_) -> true | _ -> false in
	  if is_ptr then in_old_ptr <- true;
	  in_old_term <- true;
	  self#term fmt term;
	  if is_ptr then in_old_ptr <- false;
	  in_old_term <- false
	end
      else
	(* label Post is only encoutered in post-conditions, and \at(t,Post)
	   in a post-condition is t *)
	if stringlabel = "Post" then
	  self#term fmt term
	else
	  begin
	    if current_function <> None then
	      Options.Self.warning "%a unsupported" Printer.pp_term t;
	    super#term_node fmt t
	  end
    | _ -> super#term_node fmt t	 
      
  (* modify result_varinfo when the function returns something *)
  method private compute_result_varinfo f =
    List.iter (fun stmt ->
      match stmt.skind with
      | Return(Some {enode = Lval(Var v,_)},_) -> result_varinfo <- Some v
      | _ -> ()
    ) f.sallstmts

  (* print the name of the return value for \result *)
  method! term_lval fmt t =
    match t with
    | (TResult _,_) ->
      begin
	match result_varinfo with
	| None -> failwith "term_lval: no result_varinfo" (* unreachable *)
	| Some v -> Format.fprintf fmt "%s" v.vname
      end
    | _ -> super#term_lval fmt t






  method private fundecl fmt f =
    Options.Self.debug ~dkey:Options.dkey_second_pass "IN fundecl";
    let was_ghost = is_ghost in
    let entry_point_name =
      Kernel_function.get_name (fst(Globals.entry_point())) in
    let kf = Globals.Functions.find_by_name f.svar.vname in
    let behaviors = Annotations.behaviors kf in
    let pc_assert_exception fmt pred loc msg id =
      let p = (new Sd_subst.subst)#subst_pred pred [][][] in
      let var = self#predicate_and_var fmt p in
      Format.fprintf fmt "@[<hv>%a@[<v 2>if(!%s)"
	(fun fmt -> self#line_directive ~forcefile:false fmt) loc
	var;
      Format.fprintf fmt "pathcrawler_assert_exception(\"%s\", %i);" msg id;
      Format.fprintf fmt "@]@]"
    in
    let entering_ghost = f.svar.vghost && not was_ghost in
    self#compute_result_varinfo f;
    (* BEGIN precond (entry-point) *)
    if f.svar.vname = entry_point_name then
      begin
	let x,y,z =
	  match f.svar.vtype with TFun(_,x,y,z) -> x,y,z | _ -> assert false
	in
	Format.fprintf fmt "%a@ {@\n@[<v 2>@["
	  (self#typ
	     (Some (fun fmt ->
	       Format.fprintf fmt "%s_precond" entry_point_name)))
	  (TFun(Cil.intType,x,y,z));
	List.iter (fun b ->
	  List.iter (fun pred ->
	    if b.b_assumes <> [] then
	      begin
		let vars = List.map (fun a ->
		  let p = (new Sd_subst.subst)#subst_pred a.ip_content [][][] in
		  self#predicate_and_var fmt p
		) b.b_assumes in
		Format.fprintf fmt "@[<hv>%a@[<v 2>if ("
		  (fun fmt -> self#line_directive ~forcefile:false fmt)
		  pred.ip_loc;
		List.iter (fun v -> Format.fprintf fmt "%s &&" v) vars;
		Format.fprintf fmt " 1 ) {@\n"
	      end;
	    let p = (new Sd_subst.subst)#subst_pred pred.ip_content [][][] in
	    let var = self#predicate_and_var fmt p in
	    Format.fprintf fmt "@[<hv>%a@[<v 2>if (!%s) return 0;@]@]"
	      (fun fmt -> self#line_directive ~forcefile:false fmt) pred.ip_loc
	      var;
	    if b.b_assumes <> [] then Format.fprintf fmt "}@\n@]@]"
	  ) b.b_requires;
	) behaviors;
	Format.fprintf fmt "return 1;@]@]@\n}@\n@\n"
      end;
    (* END precond (entry-point) *)
    Format.fprintf fmt "@[%t%a@\n@[<v 2>"
      (if entering_ghost then fun fmt -> Format.fprintf fmt "/*@@ ghost@ " 
       else ignore)
      self#vdecl f.svar;
    (* body. *)
    if entering_ghost then is_ghost <- true;
    (*if List.length behaviors > 0 then*) Format.fprintf fmt "@[<h 2>{@\n";
    (* BEGIN precond (not entry-point) *)
    if f.svar.vname <> entry_point_name then
      begin
	List.iter (fun b ->
	  List.iter (fun pred ->
	    let prop = Property.ip_of_requires kf Kglobal b pred in
	    if List.mem prop props then
	      let id = Prop_id.to_id prop in
	      if b.b_assumes <> [] then
		begin
		  let vars = List.map (fun a ->
		    let p =
		      (new Sd_subst.subst)#subst_pred a.ip_content [][][] in
		    self#predicate_and_var fmt p
		  ) b.b_assumes in
		  Format.fprintf fmt "@[<hv>%a@[<v 2>if ("
		    (fun fmt -> self#line_directive ~forcefile:false fmt)
		    pred.ip_loc;
		  List.iter (fun v -> Format.fprintf fmt "%s &&" v) vars;
		  Format.fprintf fmt " 1 ) {@\n"
		end;
	      pc_assert_exception
		fmt pred.ip_content pred.ip_loc "Pre-condition!" id;
	      Prop_id.translated_properties :=
		prop :: !Prop_id.translated_properties;
	      if b.b_assumes <> [] then Format.fprintf fmt "}@\n@]@]"
	  ) b.b_requires
	) behaviors
      end;
    (* END precond (not entry-point) *)
    (* BEGIN postcond *)
    postcond <-
      if List.length behaviors > 0 then
	let at_least_one_prop =
	  List.fold_left (fun res b ->
	    res ||
	      let at_least_one res (tk,pred) =
		res ||
		  let prop = Property.ip_of_ensures kf Kglobal b (tk,pred) in
		  List.mem prop props
	      in
	      List.fold_left at_least_one false b.b_post_cond
	  ) false behaviors
	in
	if at_least_one_prop then
	  Some (fun fmt ->
	    Format.fprintf fmt "@[<h 2>{@\n";
	    List.iter (fun b ->
	      List.iter (fun (tk,pred) ->
		let prop = Property.ip_of_ensures kf Kglobal b (tk,pred) in
		if List.mem prop props then
		  let id = Prop_id.to_id prop in
		  if b.b_assumes <> [] then
		    begin
		      let vars = List.map (fun a ->
			let p =
			  (new Sd_subst.subst)#subst_pred a.ip_content [][][] in
			self#predicate_and_var fmt p
		      ) b.b_assumes in
		      Format.fprintf fmt "@[<hv>%a@[<v 2>if ("
			(fun fmt -> self#line_directive ~forcefile:false fmt)
			pred.ip_loc;
		      List.iter (fun v -> Format.fprintf fmt "%s && " v) vars;
		      Format.fprintf fmt " 1) {@\n"
		    end;
		  pc_assert_exception
		    fmt pred.ip_content pred.ip_loc "Post-condition!" id;
		  Prop_id.translated_properties :=
		    prop :: !Prop_id.translated_properties;
		  if b.b_assumes <> [] then Format.fprintf fmt "}@\n@]@]@\n"
	      ) b.b_post_cond
	    ) behaviors;
	    Format.fprintf fmt "@\n}@]@\n"
	  )
	else
	  None
      else
	None;
    (* END postcond *)
    (* alloc variables for \at terms *)
    let concat_indice str ind = str ^ "[" ^ ind ^ "]" in
    begin
      try
	let tbl = Datatype.String.Hashtbl.find terms_at_Pre f.svar.vname in
	let iter_counter = ref 0 in
	Cil_datatype.Varinfo.Hashtbl.iter_sorted (fun v terms ->
	  Format.fprintf fmt "%a"
	    (self#typ(Some(fun fmt -> Format.fprintf fmt "old_%s = %s;@\n"
	      v.vname v.vname)))
	    v.vtype;
	  
	  let rec alloc_aux indices = function
	    | h :: t ->
	      let rec extract_typ =function TPtr(ty,_)->extract_typ ty | x->x in
	      let rec stars ret =function 0->ret | n -> stars (ret^"*") (n-1) in
	      let all_indices = List.fold_left concat_indice "" indices in
	      let stars =
		stars "" ((List.length terms)-(List.length indices)-1) in
	      let ty = extract_typ v.vtype in
	      Format.fprintf fmt "old_ptr_%s%s = malloc((%a)*sizeof(%a%s));@\n"
		v.vname all_indices self#term h (self#typ None)	ty stars;
	      let iterator = "__stady_iter_" ^ (string_of_int !iter_counter) in
	      Format.fprintf fmt "int %s;@\n" iterator;
	      Format.fprintf fmt "for (%s = 0; %s < %a; %s++) {@\n"
		iterator iterator self#term h iterator;
	      iter_counter := !iter_counter + 1;
	      alloc_aux (append_end indices iterator) t;
	      Format.fprintf fmt "}@\n"
	    | [] ->
	      let all_indices = List.fold_left concat_indice "" indices in
	      Format.fprintf fmt "old_ptr_%s%s = %s%s;@\n"
		v.vname all_indices v.vname all_indices
	  in
	  if Cil.isPointerType v.vtype then
	    begin
	      Format.fprintf fmt "%a"
		(self#typ(Some(fun fmt -> Format.fprintf fmt "old_ptr_%s;@\n"
		  v.vname))) v.vtype;
		alloc_aux [] terms
	      end
	) tbl
      with Not_found -> ()
    end;
    dealloc <- (* dealloc variables for \at terms *)
      Some begin fun fmt ->
	try
	  let tbl = Datatype.String.Hashtbl.find terms_at_Pre f.svar.vname in
	  let iter_counter = ref 0 in
	  Cil_datatype.Varinfo.Hashtbl.iter_sorted (fun v terms ->
	    let rec dealloc_aux indices = function
	      | [] -> ()
	      | _ :: [] ->
		let all_indices = List.fold_left concat_indice "" indices in
		Format.fprintf fmt "free(old_ptr_%s%s);@\n" v.vname all_indices
	      | h :: t ->
		let iterator = "__stady_iter_" ^(string_of_int !iter_counter) in
		Format.fprintf fmt "int %s;@\n" iterator;
		Format.fprintf fmt "for (%s = 0; %s < %a; %s++) {@\n"
		  iterator iterator self#term h iterator;
		let all_indices = List.fold_left concat_indice "" indices in
		iter_counter := !iter_counter + 1;
		let indices = append_end indices iterator in
		dealloc_aux indices t;
		Format.fprintf fmt "}@\n";
		Format.fprintf fmt "free(old_ptr_%s%s);@\n" v.vname all_indices
	    in
	    dealloc_aux [] terms
	  ) tbl
	with Not_found -> ()
      end;

    self#block ~braces:true fmt f.sbody;
    begin
      match postcond with
      | Some post_cond -> post_cond fmt; postcond <- None
      | None -> ()
    end;
    begin
      match dealloc with
      | Some de_alloc -> de_alloc fmt; dealloc <- None
      | None -> ()
    end;
    (*if List.length behaviors > 0 then*) Format.fprintf fmt "@.}";
    if entering_ghost then is_ghost <- false;
    Format.fprintf fmt "@]%t@]@."
      (if entering_ghost then fun fmt -> Format.fprintf fmt "@ */" else ignore);
    Options.Self.debug ~dkey:Options.dkey_second_pass "OUT fundecl"
  (* end of fundecl *)







      

  method! private annotated_stmt next fmt stmt =
    self#stmt_labels fmt stmt;
    let kf = Kernel_function.find_englobing_kf stmt in
    let begin_loop = ref [] in
    let end_loop = ref [] in
    let has_code_annots = List.length (Annotations.code_annot stmt) > 0 in
    let end_contract = ref [] in
    if has_code_annots then Format.fprintf fmt "{@[<h 2>@\n";
    Annotations.iter_code_annot (fun _emitter ca ->
      begin
	let behaviors =
	  match ca.annot_content with
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
	let pc_assert_exception fmt pred msg id prop =
	  let p = (new Sd_subst.subst)#subst_pnamed pred [][][] in
	  let var = self#predicate_named_and_var fmt p in
	  Format.fprintf fmt
	    "@[<v 2>if(!%s) pathcrawler_assert_exception(\"%s\", %i);@]@\n"
	    var msg id;
	  Prop_id.translated_properties :=
	    prop :: !Prop_id.translated_properties
	in
	match ca.annot_content with
	| AStmtSpec (_,bhvs) ->
	  let pc_assert_exception fmt pred msg id =
	    let p = (new Sd_subst.subst)#subst_pred pred [][][] in
	    let var = self#predicate_and_var fmt p in
	    Format.fprintf fmt
	      "@[<v 2>if(!%s) pathcrawler_assert_exception(\"%s\",%i);@]@\n"
	      var msg id
	  in
	  begin
	    if behaviors <> [] then
	      begin
		let vars = List.map (fun assumes ->
		  List.map (fun a ->
		    let p =
		      (new Sd_subst.subst)#subst_pred a.ip_content [][][] in
		    self#predicate_and_var fmt p
		  ) assumes
		) behaviors in
		Format.fprintf fmt "@[<v 2>if (";
		List.iter (fun assumes ->
		  Format.fprintf fmt "(";
		  List.iter (fun a -> Format.fprintf fmt "%s &&" a) assumes;
		  Format.fprintf fmt " 1 ) || "
		) vars;
		Format.fprintf fmt " 0 )@]{@[";
	      end;
	    List.iter (fun b ->
	      let assumes fmt =
		if b.b_assumes <> [] then
		  begin
		    let vars = List.map (fun a ->
		      let p =
			(new Sd_subst.subst)#subst_pred a.ip_content [][][] in
		      self#predicate_and_var fmt p
		    ) b.b_assumes in
		    Format.fprintf fmt "@[<v 2>if (";
		    List.iter (fun v -> Format.fprintf fmt "%s &&" v) vars;
		    Format.fprintf fmt " 1 )"
		  end
	      in
	      List.iter (fun pred ->
		let prop = Property.ip_of_requires kf (Kstmt stmt) b pred in
		if List.mem prop props then
		  begin
		    let id = Prop_id.to_id prop in
		    assumes fmt;
		    pc_assert_exception
		      fmt pred.ip_content "Stmt Pre-condition!" id;
		    Prop_id.translated_properties :=
		      prop :: !Prop_id.translated_properties;
		    Format.fprintf fmt "@]"
		  end
	      ) b.b_requires
	    ) bhvs.spec_behavior;
	    if behaviors <> [] then Format.fprintf fmt "@]}";
	  end;
	  let contract =
	    if List.length bhvs.spec_behavior > 0 then
	      let at_least_one_prop =
		List.fold_left (fun res b ->
		  if res then true
		  else
		    List.fold_left (
		      fun res (tk,pred) ->
			if res then true
			else
			  let prop = Property.ip_of_ensures
			    kf (Kstmt stmt) b (tk,pred) in
			  List.mem prop props
		    ) false b.b_post_cond
		) false bhvs.spec_behavior
	      in
	      if at_least_one_prop then
		Some (fun fmt ->
		  Format.fprintf fmt "@[<h 2>{@\n";
		  List.iter (fun b ->
		    let assumes fmt =
		      if b.b_assumes <> [] then
			begin
			  let vars = List.map (fun a ->
			    let p =
			      (new Sd_subst.subst)#subst_pred a.ip_content[][][]
			    in
			    self#predicate_and_var fmt p
			  ) b.b_assumes in
			  Format.fprintf fmt "@[<v 2>if (@[<hv>";
			  List.iter (fun v->Format.fprintf fmt "%s && " v) vars;
			  Format.fprintf fmt " 1@])@\n"
			end
		    in
		    List.iter (fun (tk,pred) ->
		      let prop = Property.ip_of_ensures
			kf (Kstmt stmt) b (tk,pred) in
		      if List.mem prop props then
			begin
			  let id = Prop_id.to_id prop in
			  assumes fmt;
			  pc_assert_exception
			    fmt pred.ip_content "Stmt Post-condition!" id;
			  Prop_id.translated_properties :=
			    prop :: !Prop_id.translated_properties;
			  Format.fprintf fmt "@]@\n"
			end
		    ) b.b_post_cond
		  ) bhvs.spec_behavior;
		  Format.fprintf fmt "@]@\n}@\n"
		)
	      else
		None
	    else
	      None in
	  begin
	    match contract with
	    | None -> ()
	    | Some c ->
	      let new_contract fmt =
		if behaviors <> [] then
		  begin
		    let vars = List.map (fun assumes ->
		      List.map (fun a ->
			let p =
			  (new Sd_subst.subst)#subst_pred a.ip_content [][][] in
			self#predicate_and_var fmt p
		      ) assumes
		    ) behaviors in
		    Format.fprintf fmt "@[<v 2>if (";
		    List.iter (fun assumes ->
		      Format.fprintf fmt "(";
		      List.iter (fun a -> Format.fprintf fmt "%s &&" a) assumes;
		      Format.fprintf fmt " 1 ) || "
		    ) vars;
		    Format.fprintf fmt " 0 )@] {@[";
		  end;
		c fmt;
		if behaviors <> [] then
		  Format.fprintf fmt "@]}"
	      in
	      end_contract := new_contract :: !end_contract
	  end
	| AAssert (_,pred) ->
	  let prop = Property.ip_of_code_annot_single kf stmt ca in
	  if List.mem prop props then
	    begin
	      let id = Prop_id.to_id prop in
	      if behaviors = [] then
		pc_assert_exception fmt pred "Assert!" id prop
	      else
		begin
		  let vars = List.map (fun assumes ->
		    List.map (fun a ->
		      let p =
			(new Sd_subst.subst)#subst_pred a.ip_content [][][] in
		      self#predicate_and_var fmt p
		    ) assumes
		  ) behaviors in
		  Format.fprintf fmt "@[<v 2>if (";
		  List.iter (fun assumes ->
		    Format.fprintf fmt "(";
		    List.iter (fun a -> Format.fprintf fmt "%s &&" a) assumes;
		    Format.fprintf fmt " 1 ) || "
		  ) vars;
		  Format.fprintf fmt " 0 )@]";
		  pc_assert_exception fmt pred "Assert!" id prop
		end
	    end
	| AInvariant (_,true,pred) ->
	  let prop = Property.ip_of_code_annot_single kf stmt ca in
	  if List.mem prop props then
	    begin
	      let id = Prop_id.to_id prop in
	      if behaviors = [] then
		begin
		  pc_assert_exception
		    fmt pred "Loop invariant not established!" id prop;
		  end_loop :=
		    (fun fmt ->
		      pc_assert_exception fmt pred
			"Loop invariant not preserved!" id prop)
		  :: !end_loop
		end
	      else
		begin
		  let vars = List.map (fun assumes ->
		    List.map (fun a ->
		      let p =
			(new Sd_subst.subst)#subst_pred a.ip_content [][][] in
		      self#predicate_and_var fmt p
		    ) assumes
		  ) behaviors in
		  Format.fprintf fmt "@[<v 2>if (";
		  List.iter (fun assumes ->
		    Format.fprintf fmt "(";
		    List.iter (fun a -> Format.fprintf fmt "%s &&" a) assumes;
		    Format.fprintf fmt " 1 ) || "
		  ) vars;
		  Format.fprintf fmt " 0 )@]";
		  pc_assert_exception
		    fmt pred "Loop invariant not established!" id prop;
		  end_loop :=
		    (fun fmt ->
		      let vars = List.map (fun assumes ->
			List.map (fun a ->
			  let p =
			    (new Sd_subst.subst)#subst_pred a.ip_content [][][]
			  in
			  self#predicate_and_var fmt p
			) assumes
		      ) behaviors in
		      Format.fprintf fmt "@[<v 2>if (";
		      List.iter (fun assumes ->
			Format.fprintf fmt "(";
			List.iter (fun a ->
			  Format.fprintf fmt "%s &&" a
			) assumes;
			Format.fprintf fmt " 1 ) || "
		      ) vars;
		      Format.fprintf fmt " 0 )@]";
		      pc_assert_exception
			fmt pred "Loop invariant not preserved!" id prop)
		  :: !end_loop
		end
	    end
	| AVariant (term,_) ->
	  let prop = Property.ip_of_code_annot_single kf stmt ca in
	  if List.mem prop props then
	    begin
	      let id = Prop_id.to_id prop in
	      Format.fprintf fmt
		"@[<v 2>if((%a)<0)pathcrawler_assert_exception(\"%s\",%i);@]@\n"
		self#term term "Variant non positive!" id;
	      Prop_id.translated_properties :=
		prop :: !Prop_id.translated_properties;
	      begin_loop :=
		(fun fmt ->
		  Format.fprintf
		    fmt "int old_variant_%i = %a;\n" id self#term term)
	      :: !begin_loop;
	      end_loop :=
		(fun fmt ->
		  Format.fprintf fmt
		    "@[<v 2>if((%a) >= old_variant_%i) pathcrawler_assert_exception(\"%s\",%i);@]@\n"
		    self#term term id "Variant non decreasing!" id;
		  Prop_id.translated_properties :=
		    prop :: !Prop_id.translated_properties)
	      :: !end_loop
	    end
	| _ -> ()
      end
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
	  match postcond with
	  | Some post_cond -> post_cond fmt; postcond <- None
	  | None -> ()
	end;
	begin
	  match dealloc with
	  | Some de_alloc -> de_alloc fmt; dealloc <- None
	  | None -> ()
	end;
	self#stmtkind next fmt stmt.skind
      | _ -> self#stmtkind next fmt stmt.skind
    end;
    List.iter (fun contract -> contract fmt) !end_contract;
    if has_code_annots then Format.fprintf fmt "@]@\n}"
  (* end of annotated_stmt *)


	


	





  method! global fmt g =
    if first_global then
      begin
	Format.fprintf fmt "extern void* malloc(unsigned);@\n";
	Format.fprintf fmt "extern void free(void*);@\n";
	first_global <- false
      end;
    match g with
    | GFun (fundec, l) ->
      if print_var fundec.svar then
	begin
	  self#in_current_function fundec.svar;
	  (* If the function has attributes then print a prototype because
	   * GCC cannot accept function attributes in a definition *)
	  let oldattr = fundec.svar.vattr in
	  (* Always pring the file name before function declarations *)
	  (* Prototype first *)
	  if oldattr <> [] then
	    (self#line_directive fmt l;
	     Format.fprintf fmt "%a;@\n" self#vdecl_complete fundec.svar);
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
      Format.fprintf fmt "/*@@@ %a@ */@\n" self#global_annotation decl
    | GText s  -> if s <> "//" then Format.fprintf fmt "%s@\n" s
  (* end of global *)
	





  (* prints a predicate and returns the name of the variable containing the
     return value *)
  method private predicate_named_and_var fmt pred_named =
    self#predicate_and_var fmt pred_named.content



  (* factorization of predicate_and_var for \exists and \forall  *)
  method private quantif_predicate_and_var ~forall fmt logic_vars hyps goal =
    if (List.length logic_vars) > 1 then
      failwith "quantification on many variables unsupported!";
    let var = "__stady_pred_" ^ (string_of_int pred_cpt) in
    let guards, vars = compute_guards [] logic_vars hyps in
    if vars <> [] then
      failwith "Unguarded variables in quantification!";
    let t1,r1,lv,r2,t2 = List.hd guards in
    let iter = lv.lv_name in
    pred_cpt <- pred_cpt + 1;
    Format.fprintf fmt "int %s = %i;@\n" var (if forall then 1 else 0);
    Format.fprintf fmt "{@\n";
    Format.fprintf fmt "int %s;@\n" iter;
    Format.fprintf fmt "for (%s = %a%s; %s %a %a && %s %s; %s++) {@\n"
      iter
      self#term t1
      (match r1 with Rlt -> "+1" | Rle -> "" | _ -> assert false)
      iter
      self#relation r2
      self#term t2
      (if forall then "" else "!")
      var
      iter;
    let goal_var = self#predicate_named_and_var fmt goal in 
    Format.fprintf fmt "if(%s(%s)) %s = %i;@\n"
      (if forall then "!" else "")
      goal_var
      var
      (if forall then 0 else 1);
    Format.fprintf fmt "}@\n";
    Format.fprintf fmt "}@\n";
    var
  (* end of quantif_predicate_and_var *)



  (* prints a predicate and returns the name of the variable containing the
     return value *)
  method private predicate_and_var fmt pred =
    match pred with
    | Ptrue -> "1"
    | Pfalse -> "0"
    | Pvalid(_,term) | Pvalid_read(_,term) ->
      let x, y = extract_terms term in
      Format.fprintf Format.str_formatter
	"((%a) >= 0 && (pathcrawler_dimension(%a) > (%a)))"
	self#term y self#term x self#term y;
      Format.flush_str_formatter()
    | Pforall(logic_vars,{content=Pimplies(hyps,goal)}) ->
      self#quantif_predicate_and_var ~forall:true fmt logic_vars hyps goal
    | Pexists(logic_vars,{content=Pand(hyps,goal)}) ->
      self#quantif_predicate_and_var ~forall:false fmt logic_vars hyps goal
    | Pforall _ -> failwith "\\forall not of the form \\forall ...; a ==> b;"
    | Pexists _ -> failwith "\\exists not of the form \\exists ...; a && b;"
    | Pnot(pred1) ->
      let pred1_var = self#predicate_named_and_var fmt pred1 in
      Format.fprintf Format.str_formatter "!(%s)" pred1_var;
      Format.flush_str_formatter()
    | Pand(pred1,pred2) ->
      let pred1_var = self#predicate_named_and_var fmt pred1 in
      let pred2_var = self#predicate_named_and_var fmt pred2 in
      Format.fprintf Format.str_formatter "(%s && %s)" pred1_var pred2_var;
      Format.flush_str_formatter()
    | Por(pred1,pred2) ->
      let pred1_var = self#predicate_named_and_var fmt pred1 in
      let pred2_var = self#predicate_named_and_var fmt pred2 in
      Format.fprintf Format.str_formatter "(%s || %s)" pred1_var pred2_var;
      Format.flush_str_formatter()
    | Pimplies(pred1,pred2) ->
      let pred1_var = self#predicate_named_and_var fmt pred1 in
      let pred2_var = self#predicate_named_and_var fmt pred2 in
      Format.fprintf Format.str_formatter "(!(%s) || %s)" pred1_var pred2_var;
      Format.flush_str_formatter()
    | Piff(pred1,pred2) ->
      let pred1_var = self#predicate_named_and_var fmt pred1 in
      let pred2_var = self#predicate_named_and_var fmt pred2 in
      Format.fprintf Format.str_formatter
	"( ( !(%s) || %s ) && ( !(%s) || %s ) )"
	pred1_var pred2_var pred2_var pred1_var;
      Format.flush_str_formatter()
    | Prel(rel,t1,t2) ->
      Format.fprintf Format.str_formatter "(%a %a %a)"
	self#term t1 self#relation rel self#term t2;
      Format.flush_str_formatter()
    | Pat (p,_) ->
      Options.Self.warning "%a unsupported!" Printer.pp_predicate pred;
      self#predicate_named_and_var fmt p
    | _ ->
      Options.Self.warning "%a unsupported" Printer.pp_predicate pred;
      "1"
(* end of pred_and_var *)
	



end (* end of printer class *)













let second_pass filename props terms_at_Pre =
  Kernel.Unicode.set false;
  let out = open_out filename in
  let fmt = Format.formatter_of_out_channel out in
  let module P = Printer_builder.Make
	(struct class printer = sd_printer props terms_at_Pre end) in
  P.pp_file fmt (Ast.get());
  flush out;
  close_out out




let pcva_emitter =
  Emitter.create "StaDyPlus" [Emitter.Property_status; Emitter.Funspec]
    ~correctness:[] ~tuning:[]













let compute_props props terms_at_Pre =
  (* Translate some parts of the pre-condition in Prolog *)
  Native_precond.translate();
  Options.Self.feedback ~dkey:Options.dkey_native_precond
    "Prolog precondition successfully generated";
  let parameters_file = Options.Precond_File.get () in
  Options.Self.feedback ~dkey:Options.dkey_native_precond
    "The result is in file %s" parameters_file;


  second_pass (Options.Temp_File.get()) props terms_at_Pre;


  let translated_properties = no_repeat !Prop_id.translated_properties in
  let test_params =
    if Sys.file_exists parameters_file then
      Printf.sprintf "-pc-test-params %s" parameters_file
    else
      ""
  in
  let cmd =
    Printf.sprintf
      "frama-c -add-path /usr/local/lib/frama-c/plugins %s -main %s -pc -pc-validate-asserts %s -pc-com %s -pc-no-xml %s"
      (Options.Temp_File.get())
      (Kernel_function.get_name (fst(Globals.entry_point())))
      test_params
      (Options.Socket_Type.get())
      (Options.PathCrawler_Options.get())
  in
  Options.Self.debug ~dkey:Options.dkey_socket "cmd: %s" cmd;
  (* open socket with the generator *)
  begin
    match Options.Socket_Type.get() with
    | s when s = "unix" ->
      let socket = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
      let name = "Pc2FcSocket" in
      begin
	try
	  Unix.bind socket (Unix.ADDR_UNIX name);
	  Unix.listen socket 1;
	  let ret = Unix.system cmd in
	  let client, _ = Unix.accept socket in
	  Pcva_socket.process_socket client;
	  Pcva_socket.print_exit_code ret
	with _ ->
	  Unix.close socket;
	  Options.Self.feedback ~dkey:Options.dkey_socket
	    "error: unix socket now closed!"
      end;
      Unix.close socket;
      Sys.remove name
    | s when s = "internet" ->
      let socket = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
      begin
	try
	  Unix.bind socket(Unix.ADDR_INET(Unix.inet_addr_loopback,2222));
	  Unix.listen socket 1;
	  let ret = Unix.system cmd in
	  let client, _ = Unix.accept socket in
	  Pcva_socket.process_socket client;
	  Pcva_socket.print_exit_code ret
	with _ ->
	  Unix.close socket;
	  Options.Self.feedback ~dkey:Options.dkey_socket
	    "error: internet socket now closed!"
      end;
      Unix.close socket
    | _ (* stdio *) ->
      let chan = Unix.open_process_in cmd in
      Pcva_socket.process_channel chan;
      let ret = Unix.close_process_in chan in
      Pcva_socket.print_exit_code ret
  end;
  States.NbCases.mark_as_computed();
  States.TestFailures.mark_as_computed();
  Options.Self.result "all-paths: %b" !Prop_id.all_paths;
  Options.Self.result "%i test cases" (States.NbCases.get());
  let hyps = [] in
  let distinct = true in
  List.iter (fun prop ->
    try
      let _ = States.TestFailures.find prop in
      let status = Property_status.False_and_reachable in
      Property_status.emit pcva_emitter ~hyps prop ~distinct status
    with
    | Not_found ->
      let status = Property_status.True in
      if !Prop_id.all_paths && (not !Prop_id.typically) then
	Property_status.emit pcva_emitter ~hyps prop ~distinct status
  ) translated_properties;
  Prop_id.translated_properties := [];
  Prop_id.all_paths := false;
  Prop_id.typically := false  









let setup_props_bijection () =
  Datatype.Int.Hashtbl.clear Prop_id.id_to_prop_tbl;
  Property.Hashtbl.clear Prop_id.prop_to_id_tbl;
  (* Bijection: unique_identifier <--> property *)
  let property_id = ref 0 in
  Property_status.iter (fun property ->
    let pos1,_ = Property.location property in
    let fc_builtin = "__fc_builtin_for_normalization.i" in
    if (Filename.basename pos1.pos_fname) <> fc_builtin then
      begin
	Datatype.Int.Hashtbl.add
	  Prop_id.id_to_prop_tbl !property_id property;
	Property.Hashtbl.add Prop_id.prop_to_id_tbl property !property_id;
	property_id := !property_id + 1
      end
  )








let properties_of_behavior name =
  Globals.Functions.fold (fun kf props ->
    Annotations.fold_behaviors (fun _ b p ->
      if b.b_name = name then
	List.rev_append (Property.ip_all_of_behavior kf Kglobal b) p
      else
	p
    ) kf props
  ) []



let properties_of_function name =
  let props = ref [] in
  Globals.Functions.iter (fun kf ->
    let kf_name = Kernel_function.get_name kf in
    if kf_name = name then
      begin
	Annotations.iter_behaviors (fun _ bhv ->
	  let new_props = Property.ip_all_of_behavior kf Kglobal bhv in
	  props := List.rev_append new_props !props
	) kf;
	let o = object
	  inherit Visitor.frama_c_inplace
	  method! vstmt_aux stmt =
	    let f s =
	      Annotations.iter_code_annot (fun _ ca ->
		let p = Property.ip_of_code_annot kf s ca in
		props := List.rev_append p !props
	      ) s;
	      s
	    in
	    Cil.ChangeDoChildrenPost(stmt, f)
	end in
	try
	  let fundec = Kernel_function.get_definition kf in
	  ignore (Visitor.visitFramacFunction o fundec)
	with _ -> ()
      end
  );
  !props



let properties_of_name name =
  let props = ref [] in
  Globals.Functions.iter (fun kf ->
    Annotations.iter_behaviors (fun _ bhv ->
      List.iter (fun id_pred ->
	if List.mem name id_pred.ip_name then
	  let p = Property.ip_of_requires kf Kglobal bhv id_pred in
	  props := p :: !props
      ) bhv.b_requires;
      List.iter (fun (tk,id_pred) ->
	if List.mem name id_pred.ip_name then
	  let p = Property.ip_of_ensures kf Kglobal bhv (tk,id_pred) in
	  props := p :: !props
      ) bhv.b_post_cond;
    ) kf;
    let o = object
      inherit Visitor.frama_c_inplace
      method! vstmt_aux stmt =
	let f s =
	  Annotations.iter_code_annot (fun _ ca ->
	    match ca.annot_content with
	    | AAssert(_,{name=l})
	    | AInvariant(_,_,{name=l}) ->
	      if List.mem name l then
		let p = Property.ip_of_code_annot kf s ca in
		props := List.rev_append p !props
	    | AStmtSpec(_,{spec_behavior=bhvs}) ->
	      List.iter (fun b ->
		List.iter (fun id_pred ->
		  if List.mem name id_pred.ip_name then
		    let p = Property.ip_of_requires kf (Kstmt s) b id_pred in
		    props := p :: !props
		) b.b_requires;
		List.iter (fun (tk,id_pred) ->
		  if List.mem name id_pred.ip_name then
		    let p =
		      Property.ip_of_ensures kf (Kstmt s) b (tk,id_pred) in
		    props := p :: !props
		) b.b_post_cond;
	      ) bhvs
	    | _ -> ()
	  ) s;
	  s
	in
	Cil.ChangeDoChildrenPost(stmt, f)
    end in
    try
      let fundec = Kernel_function.get_definition kf in
      ignore (Visitor.visitFramacFunction o fundec)
    with _ -> ()
  );
  !props




let run() =
  if Options.Enabled.get() then
    begin
      setup_props_bijection();
      let properties = Options.Properties.get () in
      let behaviors = Options.Behaviors.get () in
      let functions = Options.Functions.get () in

      let props =
	if behaviors <> [] || functions <> [] || properties <> [] then
	  begin
	    let gather p b = List.rev_append (properties_of_behavior b) p in
	    let bhv_props = List.fold_left gather [] behaviors in
	    let gather p f = List.rev_append (properties_of_function f) p in
	    let fct_props = List.fold_left gather [] functions in
	    let gather p n = List.rev_append (properties_of_name n) p in
	    let nam_props = List.fold_left gather [] properties in
	    List.rev_append bhv_props (List.rev_append fct_props nam_props)
	  end
	else
	  Property_status.fold (fun p l -> p :: l) [] 
      in

      let props = List.filter (fun p ->
	match Property_status.get p with
	| Property_status.Inconsistent _
	| Property_status.Best (Property_status.True,_)
	| Property_status.Best (Property_status.False_if_reachable,_)
	| Property_status.Best (Property_status.False_and_reachable,_) -> false
	| Property_status.Never_tried
	| Property_status.Best (Property_status.Dont_know,_) -> true
      ) props in


      Options.Self.debug ~dkey:Options.dkey_properties "selected properties:";
      List.iter (fun p ->
	try
	  let id = Prop_id.to_id p in
	  Options.Self.debug ~dkey:Options.dkey_properties
	    "%a (%i) found" Property.pretty p id
	with _ -> Options.Self.debug ~dkey:Options.dkey_properties
	  "%a not found" Property.pretty p
      ) props;

      
      let lengths = lengths_from_requires() in
      let terms_at_Pre = at_from_formals lengths in
      compute_props props terms_at_Pre;
      
      (*compute_props props;*)
      (*second_pass (Options.Temp_File.get()) props terms_at_Pre;    *)


      (* cleaning *)
      let clear_in = Cil_datatype.Varinfo.Hashtbl.clear in
      Datatype.String.Hashtbl.iter (fun _ tbl -> clear_in tbl) terms_at_Pre;
      Datatype.String.Hashtbl.clear terms_at_Pre;
      Datatype.String.Hashtbl.iter (fun _ tbl -> clear_in tbl) lengths;
      Datatype.String.Hashtbl.clear lengths;
      Datatype.Int.Hashtbl.clear Prop_id.id_to_prop_tbl;
      Property.Hashtbl.clear Prop_id.prop_to_id_tbl
    end



let extern_run () =
  Options.Enabled.set true;
  run ()

let extern_run = Dynamic.register ~plugin:"PCVA" ~journalize:true "run_pcva"
  (Datatype.func Datatype.unit Datatype.unit) extern_run


  
  
let run =
  let deps = [Ast.self; Options.Enabled.self] in
  let f, _self = State_builder.apply_once "pcva" deps run in
  f
    
let () = Db.Main.extend run
  
