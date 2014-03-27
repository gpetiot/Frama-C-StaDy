
open Cil_types


let debug_builtins = Kernel.register_category "printer:builtins"

let print_var v =
  not (Cil.is_unused_builtin v) || Kernel.is_debug_key_enabled debug_builtins

class sd_printer props terms_at_Pre () = object(self)
  inherit Printer.extensible_printer () as super

  val mutable pred_cpt = 0
  val mutable postcond = ignore
  val mutable dealloc = ignore
  val mutable result_varinfo = None
  val mutable current_function = None
  val mutable in_old_term = false
  val mutable in_old_ptr = false
  val mutable first_global = true

  (* we can only modify the property_status of the properties that have really
     been translated into pathcrawler_assert_exception *)
  val mutable translated_properties = []

  (* getter *)
  method translated_properties() = Sd_utils.no_repeat translated_properties
    
  (* unmodified *)  
  method private in_current_function vi =
    assert (current_function = None);
    current_function <- Some vi

  (* unmodified *)
  method private out_current_function =
    assert (current_function <> None);
    current_function <- None

  (* unmodified *)
  method! private opt_funspec fmt funspec =
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

  method! logic_var fmt v =
    match current_function with
    | Some f when in_old_term ->
      begin
	let prefix =
	  match v.lv_type with Ctype ty ->
	    if (Cil.isPointerType ty || Cil.isArrayType ty)
	      && in_old_ptr then "old_ptr" else "old"
	  | _ -> "old"
	in
	try
	  let tbl = Datatype.String.Hashtbl.find terms_at_Pre f.vname in
	  let vi = Extlib.the v.lv_origin in
	  ignore (Cil_datatype.Varinfo.Hashtbl.find tbl vi);
	  super#logic_var fmt {v with lv_name=prefix^"_"^v.lv_name}
	with
	| _ ->
	  Sd_options.Self.feedback ~dkey:Sd_options.dkey_at
	    "%s_%s not found in terms_at_Pre" prefix v.lv_name;
	  super#logic_var fmt v
      end
    | _ -> super#logic_var fmt v

  (* support of the litteral value of INT_MIN *)
  method! exp fmt e =
    match e.enode with
    | UnOp(Neg,{enode=Const(CInt64 (_,_,Some s))},_) when s = "2147483648" ->
      Format.fprintf fmt "(-2147483467-1)"
    | _ -> super#exp fmt e

  method private term_and_var fmt t = self#term_node_and_var fmt t

  (* \min, \max, \sum, \product and \numof *)
  method private lambda_and_var fmt li lower upper q t =
    let builtin_name = li.l_var_info.lv_name in
    let var = "__stady_term_" ^ (string_of_int pred_cpt) in
    let iter = q.lv_name in
    let init = match builtin_name with
      | s when s = "\\min" -> "-1" (* undefined here *)
      | s when s = "\\max" -> "-1" (* undefined here *)
      | s when s = "\\sum" -> "0"
      | s when s = "\\product" -> "1"
      | s when s = "\\numof" -> "0"
      | _ -> assert false
    in
    pred_cpt <- pred_cpt + 1;
    Format.fprintf fmt "int %s = %s;@\n" var init;
    Format.fprintf fmt "{@\n";
    Format.fprintf fmt "int %s;@\n" iter;
    let low = self#term_and_var fmt lower in
    let up = self#term_and_var fmt upper in
    Format.fprintf fmt "for(%s=%s; %s <= %s; %s++) {@\n" iter low iter up iter;
    let lambda_term = self#term_and_var fmt t in
    let f = match builtin_name with
      | s when s = "\\min" ->
	fun fmt -> Format.fprintf fmt "if(%s < %s) { %s = %s; }@\n"
	  lambda_term var var lambda_term
      | s when s = "\\max" ->
	fun fmt -> Format.fprintf fmt "if(%s > %s) { %s = %s; }@\n"
	  lambda_term var var lambda_term
      | s when s = "\\sum" ->
	fun fmt -> Format.fprintf fmt "%s += %s;@\n" var lambda_term
      | s when s = "\\product" ->
	fun fmt -> Format.fprintf fmt "%s *= %s;@\n" var lambda_term
      | s when s = "\\numof" ->
	fun fmt -> Format.fprintf fmt "if(%s) { %s ++; }@\n" lambda_term var
      | _ -> assert false
    in
    f fmt;
    Format.fprintf fmt "}@\n}@\n";
    var

  (* special treatment for \old terms *)
  method private term_node_and_var fmt t =
    match t.term_node with
    | Tnull -> "0"
    | TCastE (_, t') -> self#term_and_var fmt t'
    | TConst(Integer(i,_)) ->
      if (Integer.to_string i) = "-2147483648" then
	"(-2147483647-1)"
      else
	(Format.fprintf Format.str_formatter "%a" super#term_node t;
	 Format.flush_str_formatter())
    | Tapp (li,_,[lower;upper;{term_node=Tlambda([q],t)}]) ->
      self#lambda_and_var fmt li lower upper q t
    | Tapp (li,_,[param]) ->
      let var = self#term_and_var fmt param in
      let builtin_name = li.l_var_info.lv_name in
      let func_name =
	if builtin_name = "\\cos" then "cos"
	else if builtin_name = "\\abs" then "abs"
	else if builtin_name = "\\sqrt" then "sqrt"
	else assert false
      in
      Format.fprintf Format.str_formatter "%s(%s)" func_name var;
      Format.flush_str_formatter()
    | Tapp (li,_,[param1;param2]) ->
      let var1 = self#term_and_var fmt param1 in
      let var2 = self#term_and_var fmt param2 in
      let builtin_name = li.l_var_info.lv_name in
      let func_name = if builtin_name = "\\pow" then "pow" else assert false in
      Format.fprintf Format.str_formatter "%s(%s,%s)" func_name var1 var2;
      Format.flush_str_formatter()
    | Tat(_, StmtLabel _) ->
      if current_function <> None then
	Sd_options.Self.warning "%a unsupported" Printer.pp_term t;
      Format.fprintf Format.str_formatter "%a" super#term_node t;
      Format.flush_str_formatter()
    | Tat(term,LogicLabel(_,stringlabel)) ->
      if stringlabel = "Old" || stringlabel = "Pre" then
	let is_ptr =
	  match term.term_node with TLval(TMem _,_) -> true | _ -> false in
	if is_ptr then in_old_ptr <- true;
	in_old_term <- true;
	let v = self#term_and_var fmt term in
	if is_ptr then in_old_ptr <- false;
	in_old_term <- false;
	v
      else
	(* label Post is only encoutered in post-conditions, and \at(t,Post)
	   in a post-condition is t *)
	if stringlabel = "Post" || stringlabel = "Here" then
	  self#term_and_var fmt term
	else
	  begin
	    if current_function <> None then
	      Sd_options.Self.warning "%a unsupported" Printer.pp_term t;
	    Format.fprintf Format.str_formatter "%a" super#term_node t;
	    Format.flush_str_formatter()
	  end
    | TLogic_coerce (_, t) -> self#term_and_var fmt t
    | TCoerce (t, _) -> self#term_and_var fmt t
    | TLval tlval -> self#tlval_and_var fmt tlval
    | Tif (cond, then_b, else_b) ->
      let var = "__stady_pred_" ^ (string_of_int pred_cpt) in
      pred_cpt <- pred_cpt + 1;
      Format.fprintf fmt "int %s;@\n" var;
      let cond' = self#term_and_var fmt cond in
      Format.fprintf fmt "if (%s) {@\n" cond';
      let then_b' = self#term_and_var fmt then_b in
      Format.fprintf fmt "%s = %s;@\n" var then_b';
      Format.fprintf fmt "}@\n";
      Format.fprintf fmt "else {@\n";
      let else_b' = self#term_and_var fmt else_b in
      Format.fprintf fmt "%s = %s;@\n" var else_b';
      Format.fprintf fmt "}@\n";
      var
    | TConst _ ->
      Format.fprintf Format.str_formatter "%a" super#term_node t;
      Format.flush_str_formatter()
    | TBinOp(op, t1, t2) ->
      let x = self#term_and_var fmt t1 and y = self#term_and_var fmt t2 in
      Format.fprintf Format.str_formatter "(%s %a %s)" x self#binop op y;
      Format.flush_str_formatter()
    | TUnOp(op, t') ->
      let x = self#term_and_var fmt t' in
      Format.fprintf Format.str_formatter "(%a %s)" self#unop op x;
      Format.flush_str_formatter()
    | _ -> Sd_utils.error_term t
      
  method private tlval_and_var fmt (tlhost, toffset) =
    match tlhost with
    | TResult _ ->
      Format.fprintf Format.str_formatter "%a" self#term_lval (tlhost,toffset);
      Format.flush_str_formatter()
    | _ ->
      let lhost = self#term_lhost_and_var fmt tlhost in
      let offset = self#term_offset_and_var fmt toffset in
      if offset = "" then lhost else "(" ^ lhost ^ ")" ^ offset

  method private term_lhost_and_var fmt lhost =
    match lhost with
    | TVar lv ->
      Format.fprintf Format.str_formatter "%a" self#logic_var lv;
      Format.flush_str_formatter()
    | TResult _ -> assert false
    | TMem t -> let v = self#term_and_var fmt t in "*" ^ v

  method private term_offset_and_var fmt toffset =
    match toffset with
    | TNoOffset -> ""
    | TField (fi, tof) ->
      let v = self#term_offset_and_var fmt tof in
      "." ^ fi.fname ^ v
    | TModel (mi, tof) ->
      let v = self#term_offset_and_var fmt tof in
      "." ^ mi.mi_name ^ v
    | TIndex (t, tof) ->
      let t = self#term_and_var fmt t in
      let v = self#term_offset_and_var fmt tof in
      "[" ^ t ^ "]" ^ v

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

  method private at_least_one_prop kf behaviors =
    let in_ensures b r k =
      r || (List.mem (Property.ip_of_ensures kf Kglobal b k) props) in
    let in_bhv r b = r || List.fold_left (in_ensures b) false b.b_post_cond in
    List.fold_left in_bhv false behaviors

  method private fundecl fmt f =
    let was_ghost = is_ghost in
    let entry_point_name =
      Kernel_function.get_name (fst(Globals.entry_point())) in
    let kf = Globals.Functions.find_by_name f.svar.vname in
    let loc = Kernel_function.get_location kf in
    let behaviors = Annotations.behaviors kf in
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
	  let preconds =
	    List.rev_append (List.rev (Sd_utils.typically_preds b)) b.b_requires
	  in
	  let do_precond p =
	    let v = self#predicate_and_var fmt (self#subst_pred p.ip_content) in
	    Format.fprintf fmt "@[<hv>%a@[<v 2>if (!%s) return 0;@]@]@\n"
	      (fun fmt -> self#line_directive ~forcefile:false fmt) p.ip_loc v
	  in
	  if preconds <> [] then
	    begin
	      self#bhv_assumes_begin fmt b loc;
	      List.iter do_precond preconds;
	      self#bhv_assumes_end fmt b
	    end
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
    Format.fprintf fmt "@[<h 2>{@\n";
    (* BEGIN precond (not entry-point) *)
    if f.svar.vname <> entry_point_name then
      List.iter (fun b ->
	let pre = b.b_requires in
	let to_prop = Property.ip_of_requires kf Kglobal b in
	let pre = List.filter (fun p -> List.mem (to_prop p) props) pre in
	let do_precond pred =
	  let prop = to_prop pred in
	  let id = Sd_utils.to_id prop in
	  self#pc_assert_exception
	    fmt pred.ip_content pred.ip_loc "Pre-condition!" id prop
	in
	if pre <> [] then
	  begin
	    self#bhv_assumes_begin fmt b loc;
	    List.iter do_precond pre;
	    self#bhv_assumes_end fmt b
	  end
      ) behaviors;
    (* END precond (not entry-point) *)
    (* BEGIN postcond *)
    postcond <-
      if self#at_least_one_prop kf behaviors then
	fun fmt ->
	  Format.fprintf fmt "@[<h 2>{@\n";
	  List.iter (fun b ->
	    let post = b.b_post_cond in
	    let to_prop = Property.ip_of_ensures kf Kglobal b in
	    let post = List.filter (fun x -> List.mem (to_prop x) props) post in
	    let do_postcond (tk,pred) =
	      let prop = to_prop (tk,pred) in
	      let id = Sd_utils.to_id prop in
	      self#pc_assert_exception
		fmt pred.ip_content pred.ip_loc "Post-condition!" id prop
	    in
	    if post <> [] then
	      begin
		self#bhv_assumes_begin fmt b loc;
		List.iter do_postcond post;
		self#bhv_assumes_end fmt b
	      end
	  ) behaviors;
	  Format.fprintf fmt "@\n}@]@\n"
      else
	ignore;
    (* END postcond *)
    (* alloc variables for \at terms *)
    let concat_indice str ind = str ^ "[" ^ ind ^ "]" in
    let rec array_to_ptr = function
      | TArray(ty,_,_,attributes) -> TPtr(array_to_ptr ty, attributes)
      | x -> x
    in
    let dig_type = function
      | TPtr(ty,_) | TArray(ty,_,_,_) -> ty
      | _ -> assert false
    in
    begin
      try
	let tbl = Datatype.String.Hashtbl.find terms_at_Pre f.svar.vname in
	let iter_counter = ref 0 in
	Cil_datatype.Varinfo.Hashtbl.iter_sorted (fun v terms ->
	  Format.fprintf fmt "%a = %s;@\n"
	    (self#typ(Some(fun fmt -> Format.fprintf fmt "old_%s" v.vname)))
	    (array_to_ptr v.vtype)
	    v.vname;
	  let rec alloc_aux indices ty = function
	    | h :: t ->
	      let all_indices = List.fold_left concat_indice "" indices in
	      let ty = dig_type ty in
	      let h' = self#term_and_var fmt h in
	      Format.fprintf fmt "old_ptr_%s%s = malloc((%s)*sizeof(%a));@\n"
		v.vname all_indices h' (self#typ None) ty;
	      let iterator = "__stady_iter_" ^ (string_of_int !iter_counter) in
	      Format.fprintf fmt "int %s;@\n" iterator;
	      let h' = self#term_and_var fmt h in
	      Format.fprintf fmt "for (%s = 0; %s < %s; %s++) {@\n"
		iterator iterator h' iterator;
	      iter_counter := !iter_counter + 1;
	      alloc_aux (Sd_utils.append_end indices iterator) ty t;
	      Format.fprintf fmt "}@\n"
	    | [] ->
	      let all_indices = List.fold_left concat_indice "" indices in
	      Format.fprintf fmt "old_ptr_%s%s = %s%s;@\n"
		v.vname all_indices v.vname all_indices
	  in
	  if Cil.isPointerType v.vtype || Cil.isArrayType v.vtype then
	    begin
	      Format.fprintf fmt "%a;@\n"
		(self#typ(Some(fun fmt -> Format.fprintf fmt "old_ptr_%s"
		  v.vname)))
		(array_to_ptr v.vtype);
	      alloc_aux [] v.vtype terms
	    end
	) tbl
      with Not_found -> ()
    end;
    dealloc <- (* dealloc variables for \at terms *)
      (try
	 fun fmt ->
	   let tbl = Datatype.String.Hashtbl.find terms_at_Pre f.svar.vname in
	   let iter_counter = ref 0 in
	   Cil_datatype.Varinfo.Hashtbl.iter_sorted (fun v terms ->
	     let rec dealloc_aux indices = function
	       | [] -> ()
	       | _ :: [] ->
		 let all_indices = List.fold_left concat_indice "" indices in
		 Format.fprintf fmt "free(old_ptr_%s%s);@\n" v.vname all_indices
	       | h :: t ->
		 let iterator = "__stady_iter_"^(string_of_int !iter_counter) in
		 Format.fprintf fmt "int %s;@\n" iterator;
		 let h' = self#term_and_var fmt h in
		 Format.fprintf fmt "for (%s = 0; %s < %s; %s++) {@\n"
		   iterator iterator h' iterator;
		 let all_indices = List.fold_left concat_indice "" indices in
		 iter_counter := !iter_counter + 1;
		 let indices = Sd_utils.append_end indices iterator in
		 dealloc_aux indices t;
		 Format.fprintf fmt "}@\n";
		 Format.fprintf fmt "free(old_ptr_%s%s);@\n" v.vname all_indices
	     in
	     dealloc_aux [] terms
	   ) tbl
       with Not_found -> ignore);
    self#block ~braces:true fmt f.sbody;
    postcond fmt;
    postcond <- ignore;
    dealloc fmt;
    dealloc <- ignore;
    Format.fprintf fmt "@.}";
    if entering_ghost then is_ghost <- false;
    Format.fprintf fmt "@]%t@]@."
      (if entering_ghost then fun fmt -> Format.fprintf fmt "@ */" else ignore)
  (* end of fundecl *)

  method private subst_pred p = (new Sd_subst.subst)#subst_pred p [] [] [] []

  method private bhv_assumes_begin fmt bhv loc =
    if bhv.b_assumes <> [] then
      let f a = self#predicate_and_var fmt (self#subst_pred a.ip_content) in
      let vars = List.map f bhv.b_assumes in
      Format.fprintf fmt "@[<hv>%a@[<v 2>if ("
	(fun fmt -> self#line_directive ~forcefile:false fmt) loc;
      List.iter (fun v -> Format.fprintf fmt "%s && " v) vars;
      Format.fprintf fmt "1) {@\n"
	
  method private bhv_assumes_end fmt bhv =
    if bhv.b_assumes <> [] then Format.fprintf fmt "}@]@]@\n"

  method private pc_assert_exception fmt pred loc msg id prop =
    let var = self#predicate_and_var fmt (self#subst_pred pred) in
    Format.fprintf fmt "@[<hv>%a@[<v 2>if(!%s)"
      (fun fmt -> self#line_directive ~forcefile:false fmt) loc var;
    Format.fprintf fmt "pathcrawler_assert_exception(\"%s\", %i);" msg id;
    Format.fprintf fmt "@]@]@\n";
    translated_properties <- prop :: translated_properties

  method private bhv_guard_begin fmt behaviors loc =
    if behaviors <> [] then
      let f a = self#predicate_and_var fmt (self#subst_pred a.ip_content) in
      let g assumes_list = List.map f assumes_list in
      let vars = List.map g behaviors in
      Format.fprintf fmt "@[<hv>%a@[<v 2>if ("
	(fun fmt -> self#line_directive ~forcefile:false fmt) loc;
      List.iter (fun assumes ->
	Format.fprintf fmt "(";
	List.iter (fun a -> Format.fprintf fmt "%s && " a) assumes;
	Format.fprintf fmt "1 ) || "
      ) vars;
      Format.fprintf fmt "0) {@\n"

  method private bhv_guard_end fmt behaviors =
    if behaviors <> [] then Format.fprintf fmt "}@]@]@\n"

  method! private annotated_stmt next fmt stmt =
    Format.pp_open_hvbox fmt 2;
    self#stmt_labels fmt stmt;
    Format.pp_open_hvbox fmt 0;
    let kf = Kernel_function.find_englobing_kf stmt in
    let begin_loop = ref [] in
    let end_loop = ref [] in
    let has_code_annots = List.length (Annotations.code_annot stmt) > 0 in
    let end_contract = ref [] in
    let loc = Cil_datatype.Stmt.loc stmt in
    if has_code_annots then Format.fprintf fmt "%a@[<v 2>{@\n"
      (fun fmt -> self#line_directive ~forcefile:false fmt) loc;
    Annotations.iter_code_annot (fun _ ca ->
      let bhv_names =
	match ca.annot_content with
	| AAssert (b,_) | AStmtSpec (b,_) | AInvariant (b,_,_) -> b
	| _ -> []
      in
      let behaviors =
	List.map (fun bname ->
	  Annotations.fold_behaviors (fun _ b ret ->
	    if b.b_name = bname then b.b_assumes else ret
	  ) kf []
	) bhv_names
      in
      match ca.annot_content with
      | AStmtSpec (_,bhvs) ->
	self#bhv_guard_begin fmt behaviors loc;
	List.iter (fun b ->
	  let pre = b.b_requires in
	  let to_prop = Property.ip_of_requires kf (Kstmt stmt) b in
	  let pre = List.filter (fun p -> List.mem (to_prop p) props) pre in
	  let do_precond pred =
	    let prop = to_prop pred in
	    let id = Sd_utils.to_id prop in
	    self#pc_assert_exception fmt pred.ip_content pred.ip_loc
	      "Stmt Pre-condition!" id prop
	  in
	  if pre <> [] then
	    begin
	      self#bhv_assumes_begin fmt b loc;
	      List.iter do_precond pre;
	      self#bhv_assumes_end fmt b
	    end
	) bhvs.spec_behavior;
	self#bhv_guard_end fmt behaviors;
	let contract =
	  if self#at_least_one_prop kf bhvs.spec_behavior then
	    fun fmt ->
	      self#bhv_guard_begin fmt behaviors loc;
	      Format.fprintf fmt "%a@[<v 2>{@\n"
		(fun fmt -> self#line_directive ~forcefile:false fmt) loc;
	      List.iter (fun b ->
		let post = b.b_post_cond in
		let to_prop = Property.ip_of_ensures kf (Kstmt stmt) b in
		let post =
		  List.filter (fun x -> List.mem (to_prop x) props) post in
		let do_postcond ((_,pred) as k) =
		  let prop = to_prop k in
		  let id = Sd_utils.to_id prop in
		  self#pc_assert_exception fmt pred.ip_content pred.ip_loc
		    "Stmt Post-condition!" id prop
		in
		if post <> [] then
		  begin
		    self#bhv_assumes_begin fmt b loc;
		    List.iter do_postcond post;
		    self#bhv_assumes_end fmt b
		  end
	      ) bhvs.spec_behavior;
	      Format.fprintf fmt "}@\n @]";
	      self#bhv_guard_end fmt behaviors
	  else
	    ignore
	in
	end_contract := contract :: !end_contract
      | AAssert (_,pred) ->
	let prop = Property.ip_of_code_annot_single kf stmt ca in
	if List.mem prop props then
	  let id = Sd_utils.to_id prop in
	  self#bhv_guard_begin fmt behaviors loc;
	  self#pc_assert_exception fmt pred.content pred.loc "Assert!" id prop;
	  self#bhv_guard_end fmt behaviors
      | AInvariant (_,true,pred) ->
	let prop = Property.ip_of_code_annot_single kf stmt ca in
	if List.mem prop props then
	  let id = Sd_utils.to_id prop in
	  let f fmt msg =
	    self#bhv_guard_begin fmt behaviors loc;
	    self#pc_assert_exception fmt pred.content pred.loc msg id prop;
	    self#bhv_guard_end fmt behaviors
	  in
	  f fmt "Loop invariant not established!";
	  end_loop :=
	    (fun fmt -> f fmt "Loop invariant not preserved!") :: !end_loop
      | AVariant (term,_) ->
	let prop = Property.ip_of_code_annot_single kf stmt ca in
	if List.mem prop props then
	  let id = Sd_utils.to_id prop in
	  let term' = self#term_and_var fmt term in
	  Format.fprintf fmt "@[<hv>%a@[<v 2>if ((%s) < 0)"
	    (fun fmt -> self#line_directive ~forcefile:false fmt) loc term';
	  Format.fprintf fmt
	    "pathcrawler_assert_exception(\"Variant non positive\",%i);" id;
	  Format.fprintf fmt "@]@]";
	  translated_properties <- prop :: translated_properties;
	  begin_loop :=
	    (fun fmt ->
	      let term' = self#term_and_var fmt term in
	      Format.fprintf fmt "int old_variant_%i = %s;@\n" id term')
	  :: !begin_loop;
	  end_loop :=
	    (fun fmt ->
	      Format.fprintf fmt "@[<hv>%a@[<v 2>if ((old_variant_%i) < 0)"
		(fun fmt -> self#line_directive ~forcefile:false fmt) loc id;
	      Format.fprintf fmt
		"pathcrawler_assert_exception(\"Variant non positive\",%i);"
		id;
	      Format.fprintf fmt "@]@]";
	      let term' = self#term_and_var fmt term in
	      Format.fprintf fmt "@[<hv>%a@[<v 2>if ((%s) >= old_variant_%i)"
		(fun fmt -> self#line_directive ~forcefile:false fmt) loc
		term' id;
	      Format.fprintf fmt
		"pathcrawler_assert_exception(\"Variant non decreasing\",%i);"
		id;
	      Format.fprintf fmt "@]@]";
	      translated_properties <- prop :: translated_properties)
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
	postcond fmt;
	postcond <- ignore;
	dealloc fmt;
	dealloc <- ignore;
	self#stmtkind next fmt stmt.skind
      | _ -> self#stmtkind next fmt stmt.skind
    end;
    List.iter (fun contract -> contract fmt) !end_contract;
    if has_code_annots then Format.fprintf fmt "}@\n @]";
    Format.pp_close_box fmt ();
    Format.pp_close_box fmt ()
  (* end of annotated_stmt *)

  method! global fmt g =
    if first_global then
      begin
	Format.fprintf fmt
	  "extern int pathcrawler_assert_exception(char*,int);@\n";
	Format.fprintf fmt "extern int pathcrawler_dimension(void*);@\n";
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
    (* print global variable 'extern' declarations, and function prototypes *)
    | GVarDecl (funspec, vi, l) ->
      if print_var vi then
	begin
	  if Cil.isFunctionType vi.vtype then self#in_current_function vi;
	  self#opt_funspec fmt funspec;
	  self#line_directive fmt l;
	  Format.fprintf fmt "%a@\n@\n" self#vdecl_complete vi;
	  if Cil.isFunctionType vi.vtype then self#out_current_function
	end
    | _ -> super#global fmt g
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
    let guards, vars = Sd_utils.compute_guards [] logic_vars hyps in
    if vars <> [] then
      failwith "Unguarded variables in quantification!";
    let t1,r1,lv,r2,t2 = List.hd guards in
    let iter = lv.lv_name in
    pred_cpt <- pred_cpt + 1;
    Format.fprintf fmt "int %s = %i;@\n" var (if forall then 1 else 0);
    Format.fprintf fmt "{@\n";
    Format.fprintf fmt "int %s;@\n" iter;
    let t1' = self#term_and_var fmt t1 in
    let t2' = self#term_and_var fmt t2 in
    Format.fprintf fmt "for (%s = %s%s; %s %a %s && %s %s; %s++) {@\n"
      iter
      t1'
      (match r1 with Rlt -> "+1" | Rle -> "" | _ -> assert false)
      iter
      self#relation r2
      t2'
      (if forall then "" else "!")
      var
      iter;
    let goal_var = self#predicate_named_and_var fmt goal in 
    Format.fprintf fmt "%s = %s;@\n" var goal_var;
    Format.fprintf fmt "}@\n}@\n";
    var
  (* end of quantif_predicate_and_var *)

  (* prints a predicate and returns the name of the variable containing the
     return value *)
  method private predicate_and_var fmt pred =
    match pred with
    | Ptrue -> "1"
    | Pfalse -> "0"
    | Pvalid(_,term) | Pvalid_read(_,term) ->
      let x, y = Sd_utils.extract_terms term in
      let x',y' = self#term_and_var fmt x, self#term_and_var fmt y in
      Format.fprintf Format.str_formatter
	"(%s >= 0 && pathcrawler_dimension(%s) > %s)"
	y' x' y';
      Format.flush_str_formatter()
    | Pforall(logic_vars,{content=Pimplies(hyps,goal)}) ->
      self#quantif_predicate_and_var ~forall:true fmt logic_vars hyps goal
    | Pexists(logic_vars,{content=Pand(hyps,goal)}) ->
      self#quantif_predicate_and_var ~forall:false fmt logic_vars hyps goal
    | Pforall _ -> failwith "\\forall not of the form \\forall ...; a ==> b;"
    | Pexists _ -> failwith "\\exists not of the form \\exists ...; a && b;"
    | Pnot(pred1) ->
      let pred1_var = self#predicate_named_and_var fmt pred1 in
      Format.fprintf Format.str_formatter "(! %s)" pred1_var;
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
      let var = "__stady_pred_" ^ (string_of_int pred_cpt) in
      pred_cpt <- pred_cpt + 1;
      Format.fprintf fmt "int %s = 1;@\n" var;
      let pred1_var = self#predicate_named_and_var fmt pred1 in
      Format.fprintf fmt "if (%s) {@\n" pred1_var;
      let pred2_var = self#predicate_named_and_var fmt pred2 in
      Format.fprintf fmt "%s = %s;@\n" var pred2_var;
      Format.fprintf fmt "}@\n";
      var
    | Piff(pred1,pred2) ->
      let pred1_var = self#predicate_named_and_var fmt pred1 in
      let pred2_var = self#predicate_named_and_var fmt pred2 in
      Format.fprintf Format.str_formatter
	"( ( (!%s) || %s ) && ( (!%s) || %s ) )"
	pred1_var pred2_var pred2_var pred1_var;
      Format.flush_str_formatter()
    | Prel(rel,t1,t2) ->
      let t1', t2' = self#term_and_var fmt t1, self#term_and_var fmt t2 in
      Format.fprintf Format.str_formatter "(%s %a %s)"
	t1' self#relation rel t2';
      Format.flush_str_formatter()
    | Pat (p,_) ->
      Sd_options.Self.warning "%a unsupported!" Printer.pp_predicate pred;
      self#predicate_named_and_var fmt p
    | _ ->
      Sd_options.Self.warning "%a unsupported" Printer.pp_predicate pred;
      "1"
(* end of pred_and_var *)
end (* end of printer class *)
