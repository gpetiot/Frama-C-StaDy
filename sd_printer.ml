
open Cil_types


let debug_builtins = Kernel.register_category "printer:builtins"

let print_var v =
  not (Cil.is_unused_builtin v) || Kernel.is_debug_key_enabled debug_builtins


(* Extracts the varinfo of the variable and its inferred size as a term
   from a term t as \valid(t). *)
let rec extract_from_valid : term -> varinfo * term =
  fun t -> match t.term_node with
  | TBinOp (((PlusPI|IndexPI|MinusPI) as op),
    	    ({term_node=TCastE((TPtr _) as ty,t)} as _operand1),
    	    ({term_node=(Trange (_, Some _))} as operand2)) ->
      extract_from_valid
    	{t with term_node=TBinOp(op, {t with term_type=Ctype ty}, operand2)}
  | TBinOp((PlusPI|IndexPI),
	   ({term_node=TLval(TVar v, _)}),
	   ({term_node=
	       Trange(_,
		      Some {term_node=
			  TBinOp (MinusA, x,
				  {term_node=TConst (Integer (i, _))})})}))
      when Integer.equal i Integer.one ->
    let varinfo = Extlib.the v.lv_origin in
    varinfo, x
  | TBinOp((PlusPI|IndexPI),
	   ({term_node=TLval(TVar v, _)}),
	   ({term_node=Trange(_,Some bound)})) ->
    let varinfo = Extlib.the v.lv_origin in
    let tnode = TBinOp (PlusA, bound, Cil.lone ~loc:t.term_loc()) in
    let einfo = {exp_type=bound.term_type; exp_name=[]} in
    let term = Cil.term_of_exp_info t.term_loc tnode einfo in
    varinfo, term
  | TBinOp((PlusPI|IndexPI),
	   ({term_node=TLval(TVar v, _)}),
	   (t2 (* anything but a Trange *))) ->
    let varinfo = Extlib.the v.lv_origin in
    let tnode = TBinOp (PlusA, t2, Cil.lone ~loc:t.term_loc()) in
    let einfo = {exp_type=t2.term_type; exp_name=[]} in
    let term = Cil.term_of_exp_info t.term_loc tnode einfo in
    varinfo, term
  | TBinOp((PlusPI|IndexPI),
	   ({term_node=TLval tlval}),
	   ({term_node=
	       Trange(_,
		      Some {term_node=
			  TBinOp (MinusA, x,
				  {term_node=TConst (Integer (i, _))})})}))
      when Integer.equal i Integer.one ->
    let varinfo, _ = extract_from_valid {t with term_node=TLval tlval} in
    varinfo, x
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
  | TStartOf _ -> Sd_options.Self.abort "TStartOf \\valid(%a)" Printer.pp_term t
  | TAddrOf _ -> Sd_options.Self.abort "TAddrOf \\valid(%a)" Printer.pp_term t
  | TCoerce _ -> Sd_options.Self.abort "TCoerce \\valid(%a)" Printer.pp_term t
  | TCoerceE _ -> Sd_options.Self.abort "TCoerceE \\valid(%a)" Printer.pp_term t
  | TLogic_coerce _ ->
    Sd_options.Self.abort "TLogic_coerce \\valid(%a)" Printer.pp_term t
  | TBinOp _ -> Sd_options.Self.abort "TBinOp \\valid(%a)" Printer.pp_term t
  | _ -> Sd_options.Self.abort "\\valid(%a)" Printer.pp_term t


(* Computes and returns a hashtable such that :
   -  var1 => inferred size for var1
   -  var2 => inferred size for var2
   -  ...
   - var n => inferred size for varn *)
let lengths_from_requires :
    kernel_function -> term list Cil_datatype.Varinfo.Hashtbl.t =
  fun kf ->
    let vi = Kernel_function.get_vi kf in
    let kf_tbl = Cil_datatype.Varinfo.Hashtbl.create 32 in
    let o = object
      inherit Visitor.frama_c_inplace
      method! vpredicate p =
	match p with
	| Pvalid(_, t) | Pvalid_read(_, t) ->
	  begin
	    try
	      let v, term = extract_from_valid t in
	      let terms =
		try Cil_datatype.Varinfo.Hashtbl.find kf_tbl v
		with Not_found -> []
	      in
	      let terms = Sd_utils.append_end terms term in
	      Cil_datatype.Varinfo.Hashtbl.replace kf_tbl v terms;
	      Cil.DoChildren
	    with
	    | _ -> Cil.DoChildren
	  end
	| _ -> Cil.DoChildren
    end
    in
    let on_requires p =
      let p' = (new Sd_subst.subst)#subst_pred p.ip_content [][][][] in
      ignore (Visitor.visitFramacPredicate o p')
    in
    let on_bhv _ bhv = List.iter on_requires bhv.b_requires in
    if not (Cil.is_unused_builtin vi) then
      (* TODO: handle arrays with constant size *)
      (*Globals.Vars.iter (fun vi _ -> () );*)
      Annotations.iter_behaviors on_bhv kf;
    kf_tbl


class sd_printer props () = object(self)
  inherit Printer.extensible_printer () as super

  val mutable pred_cpt = 0
  val mutable term_cpt = 0
  val mutable gmp_cpt = 0
  val mutable postcond : Format.formatter -> unit = ignore
  val mutable dealloc : Format.formatter -> unit = ignore
  val mutable result_varinfo = None
  val mutable current_function = None
  val mutable in_old_term = false
  val mutable in_old_ptr = false
  val mutable first_global = true
  val mutable bhv_to_reach_cpt = 0
  val mutable visited_globals = []

  (* list of (stmtkind * stmt) used for testing reachibility of some stmts *)
  val mutable stmts_to_reach = []

  (* we can only modify the property_status of the properties that have really
     been translated into pathcrawler_assert_exception *)
  val mutable translated_properties = []

  method private fresh_pred_var() =
    let var = "__stady_pred_" ^ (string_of_int pred_cpt) in
    pred_cpt <- pred_cpt + 1;
    var

  method private fresh_term_var() =
    let var = "__stady_term_" ^ (string_of_int term_cpt) in
    term_cpt <- term_cpt + 1;
    var

  method private fresh_gmp_var() =
    let var = "__stady_gmp_" ^ (string_of_int gmp_cpt) in
    gmp_cpt <- gmp_cpt + 1;
    var

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
    | Some _ when in_old_term ->
      begin
	let prefix =
	  match v.lv_type with Ctype ty ->
	    if (Cil.isPointerType ty || Cil.isArrayType ty)
	      && in_old_ptr then "old_ptr" else "old"
	  | _ -> "old"
	in
	match v.lv_origin with
	  Some _ -> super#logic_var fmt {v with lv_name=prefix^"_"^v.lv_name}
	| None -> super#logic_var fmt v
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
    let var = self#fresh_gmp_var() in
    let iter = q.lv_name in
    let init_val = match builtin_name with
      | s when s = "\\sum" -> "0"
      | s when s = "\\product" -> "1"
      | s when s = "\\numof" -> "0"
      | _ -> assert false (* unreachable *)
    in
    Format.fprintf fmt "mpz_t %s;@\n" var;
    Format.fprintf fmt "__gmpz_init_set_si(%s, %s);@\n" var init_val;
    Format.fprintf fmt "{@\n";
    let low = self#term_and_var fmt lower in
    let up = self#term_and_var fmt upper in
    begin
      match lower.term_type with
      | Linteger ->
	begin
	  match upper.term_type with
	  | Linteger ->
	    Format.fprintf fmt "mpz_t %s;@\n" iter;
	    Format.fprintf fmt "__gmpz_init_set(%s, %s);@\n" iter low;
	    Format.fprintf fmt "for(; __gmpz_cmp(%s, %s) <= 0;) {@\n" iter up;
	    let lambda_term = self#term_and_var fmt t in
	    let f = match builtin_name with
	      | s when s = "\\sum" ->
		fun fmt -> Format.fprintf fmt "__gmpz_add(%s, %s, %s);@\n"
		  var var lambda_term
	      | s when s = "\\product" ->
		fun fmt -> Format.fprintf fmt "__gmpz_mult(%s, %s, %s);@\n"
		  var var lambda_term
	      | s when s = "\\numof" ->
		(* lambda_term is of type:
		   Ltype (lt,_) when lt.lt_name = Utf8_logic.boolean *)
		fun fmt -> Format.fprintf fmt
		  "if(%s) __gmpz_add_ui(%s, %s, 1);@\n" lambda_term var var
	      | _ -> assert false
	    in
	    f fmt;
	    Format.fprintf fmt "__gmpz_add_ui(%s, %s, 1);@\n" iter iter;
	    if builtin_name <> "\\numof" then
	      Format.fprintf fmt "__gmpz_clear(%s);@\n" lambda_term;
	    Format.fprintf fmt "}@\n";
	    Format.fprintf fmt "__gmpz_clear(%s);@\n" iter;
	    Format.fprintf fmt "__gmpz_clear(%s);@\n" low;
	    Format.fprintf fmt "__gmpz_clear(%s);@\n" up;
	    Format.fprintf fmt "}@\n";
	    var
	  | Lreal -> assert false (* unreachable *)
	  | _ -> assert false (* unreachable ? *)
	end
      | Lreal -> assert false (* unreachable *)
      | _ -> assert false (* unreachable ? *)
    end

  method private term_node_and_var fmt t =
    let ty = match t.term_type with
      | Ctype c -> Ctype (Cil.unrollType c)
      | x -> x
    in
    match t.term_node with

    | TConst _ ->
      begin
	match ty with
	| Linteger ->
	  let var = self#fresh_gmp_var() in
	  Format.fprintf fmt "mpz_t %s;@\n" var;
	  Format.fprintf fmt "__gmpz_init_set_str(%s, \"%a\", 10);@\n"
	    var self#term t;
	  var
	| Lreal -> assert false (* TODO: reals *)
	| _ ->
	  (Format.fprintf Format.str_formatter "%a" super#term_node t;
	   Format.flush_str_formatter())
      end

    | TLval tlval ->
      begin
	match ty with
	| Linteger ->
	  let var = self#fresh_gmp_var() in
	  let t' = self#tlval_and_var fmt tlval in
	  Format.fprintf fmt "mpz_t %s;@\n" var;
	  Format.fprintf fmt "__gmpz_init_set(%s, %s);@\n" var t';
	  var
	| Lreal -> assert false (* TODO: reals *)
	| _ -> self#tlval_and_var fmt tlval
      end

    | TSizeOf _
    | TSizeOfE _
    | TSizeOfStr _
    | TAlignOf _
    | TAlignOfE _ ->
      Format.fprintf Format.str_formatter "%a" super#term_node t;
      Format.flush_str_formatter()

    | TUnOp(op, t') ->
      begin
	match ty with
	| Linteger ->
	  assert(op = Neg);
	  let x = self#term_and_var fmt t' in
	  let var = self#fresh_gmp_var() in
	  Format.fprintf fmt "mpz_t %s;@\n" var;
	  Format.fprintf fmt "__gmpz_init(%s);@\n" var;
	  begin
	    match t'.term_type with
	    | Linteger ->
	      Format.fprintf fmt "__gmpz_ui_sub(%s, 0, %s);@\n" var x;
	      Format.fprintf fmt "__gmpz_clear(%s);@\n" x
	    | Lreal -> assert false (* unreachable *)
	    | Ctype(TInt((IULongLong|IULong|IUShort|IUInt|IUChar),_)) ->
	      let var' = self#fresh_gmp_var() in
	      Format.fprintf fmt "mpz_t %s;@\n" var';
	      Format.fprintf fmt "__gmpz_init_set_ui(%s, %s);@\n" var' x;
	      Format.fprintf fmt "__gmpz_ui_sub(%s, 0, %s);@\n" var var';
	      Format.fprintf fmt "__gmpz_clear(%s);@\n" var'
	    | Ctype(TInt _) ->
	      let var' = self#fresh_gmp_var() in
	      Format.fprintf fmt "mpz_t %s;@\n" var';
	      Format.fprintf fmt "__gmpz_init_set_si(%s, %s);@\n" var' x;
	      Format.fprintf fmt "__gmpz_ui_sub(%s, 0, %s);@\n" var var';
	      Format.fprintf fmt "__gmpz_clear(%s);@\n" var'
	    | _ -> assert false (* unreachable *)
	  end;
	  var
	| Lreal -> assert false (* TODO: reals *)
	| _ ->
	  let x = self#term_and_var fmt t' in
	  Format.fprintf Format.str_formatter "(%a %s)" self#unop op x;
	  Format.flush_str_formatter()
      end

    | TBinOp((IndexPI|PlusPI|MinusPI) as op, t1, t2) ->
      begin
	match t2.term_type with
	| Linteger ->
	  let x = self#term_and_var fmt t1 and y = self#term_and_var fmt t2 in
	  let var = self#fresh_term_var() in
	  Format.fprintf fmt "int %s = __gmpz_get_si(%s);@\n" var y;
	  Format.fprintf fmt "__gmpz_clear(%s);@\n" y;
	  Format.fprintf Format.str_formatter "(%s %a %s)" x self#binop op var;
	  Format.flush_str_formatter()
	| Lreal -> assert false (* unreachable *)
	| _ ->
	  let x = self#term_and_var fmt t1 and y = self#term_and_var fmt t2 in
	  Format.fprintf Format.str_formatter "(%s %a %s)" x self#binop op y;
	  Format.flush_str_formatter()
      end

    | TBinOp(op, t1, t2) ->
      begin
	match ty with
	| Linteger ->
	  let x = self#term_and_var fmt t1 and y = self#term_and_var fmt t2 in
	  let var = self#fresh_gmp_var() in
	  Format.fprintf fmt "mpz_t %s;@\n" var;
	  Format.fprintf fmt "__gmpz_init(%s);@\n" var;
	  let op' = match op with
	    | PlusA -> "__gmpz_add"
	    | MinusA -> "__gmpz_sub"
	    | Mult -> "__gmpz_mul"
	    | Div -> "__gmpz_tdiv_q"
	    | Mod -> "__gmpz_tdiv_r"
	    | _ -> assert false
	  in
	  begin
	    match t1.term_type, t2.term_type with
	    | Linteger, Linteger ->
	      Format.fprintf fmt "%s(%s, %s, %s);@\n" op' var x y;
	      Format.fprintf fmt "__gmpz_clear(%s);@\n" x;
	      Format.fprintf fmt "__gmpz_clear(%s);@\n" y;
	      var
	    | Linteger,Ctype(TInt((IULongLong|IULong|IUShort|IUInt|IUChar),_))->
	      Format.fprintf fmt "%s_ui(%s, %s, %s);@\n" op' var x y;
	      Format.fprintf fmt "__gmpz_clear(%s);@\n" x;
	      var
	    | Linteger, Ctype (TInt _) ->
	      Format.fprintf fmt "%s_si(%s, %s, %s);@\n" op' var x y;
	      Format.fprintf fmt "__gmpz_clear(%s);@\n" x;
	      var
	    | Ctype(TInt((IULongLong|IULong|IUShort|IUInt|IUChar),_)),Linteger->
	      if op = PlusA || op = Mult then
		begin
		  Format.fprintf fmt "%s_ui(%s, %s, %s);@\n" op' var y x;
		  Format.fprintf fmt "__gmpz_clear(%s);@\n" y;
		  var
		end
	      else
		assert false (* TODO *)
	    | Ctype (TInt _), Linteger ->
	      if op = PlusA || op = Mult then
		begin
		  Format.fprintf fmt "%s_si(%s, %s, %s);@\n" op' var y x;
		  Format.fprintf fmt "__gmpz_clear(%s);@\n" y;
		  var
		end
	      else
		assert false (* TODO *)
	    | Ctype(TInt _), Ctype(TInt _) ->
	      let var1 = self#fresh_gmp_var() in
	      let var2 = self#fresh_gmp_var() in
	      Format.fprintf fmt "mpz_t %s, %s;@\n" var1 var2;
	      Format.fprintf fmt "__gmpz_init_set_si(%s, %s);@\n" var1 x;
	      Format.fprintf fmt "__gmpz_init_set_si(%s, %s);@\n" var2 y;
	      Format.fprintf fmt "%s(%s, %s, %s);@\n" op' var var1 var2;
	      Format.fprintf fmt "__gmpz_clear(%s);@\n" var1;
	      Format.fprintf fmt "__gmpz_clear(%s);@\n" var2;
	      var
	    | _ -> assert false
	  end
	| Lreal -> assert false (* TODO: reals *)
	| Ltype (lt,_) when lt.lt_name = Utf8_logic.boolean ->
	  begin
	    match t1.term_type, t2.term_type with
	    | Linteger, Linteger ->
	      let var = self#fresh_term_var() in
	      let x = self#term_and_var fmt t1 in
	      let y = self#term_and_var fmt t2 in
	      Format.fprintf fmt "int %s = __gmpz_cmp(%s, %s) %a 0;@\n"
		var x y self#binop op;
	      Format.fprintf fmt "__gmpz_clear(%s);@\n" x;
	      Format.fprintf fmt "__gmpz_clear(%s);@\n" y;
	      var
	    | _ ->
	      let x = self#term_and_var fmt t1 in
	      let y = self#term_and_var fmt t2 in
	      Format.fprintf Format.str_formatter "(%s %a %s)"
		x self#binop op y;
	      Format.flush_str_formatter()
	  end
	| _ -> assert false (* unreachable ? *)
      end

    | TCastE (ty', t') ->
      begin
	match t'.term_type with (* source type *)
	| Linteger ->
	  begin
	    match ty with (* dest type *)
	    | Ctype (TInt((IULongLong|IULong|IUShort|IUInt|IUChar),_)) ->
	      let v = self#term_and_var fmt t' in
	      let var = self#fresh_term_var() in
	      Format.fprintf fmt "%a %s = __gmpz_get_ui(%s);@\n"
		(self#typ None) ty' var v;
	      Format.fprintf fmt "__gmpz_clear(%s);@\n" v;
	      var
	    | Ctype (TInt _) ->
	      let v = self#term_and_var fmt t' in
	      let var = self#fresh_term_var() in
	      Format.fprintf fmt "%a %s = __gmpz_get_si(%s);@\n"
		(self#typ None) ty' var v;
	      Format.fprintf fmt "__gmpz_clear(%s);@\n" v;
	      var
	    | _ -> assert false (* unreachable *)
	  end
	| Lreal -> assert false (* reals *)
	| Ctype _ ->
	  let v = self#term_and_var fmt t' in
	  Format.fprintf Format.str_formatter "(%a)%s" (self#typ None) ty' v;
	  Format.flush_str_formatter()
	| _ -> assert false (* unreachable *)
      end

    | TAddrOf _
    | TStartOf _ ->
      Format.fprintf Format.str_formatter "%a" super#term_node t;
      Format.flush_str_formatter()

    | Tapp (li, _ (* already substituted *), params) ->
      let builtin_name = li.l_var_info.lv_name in
      begin
	match ty with
	  | Linteger ->
	    if builtin_name = "\\abs" then
	      begin
		let param = List.hd params in
		assert (List.tl params = []);
		let x = self#term_and_var fmt param in
		let var = self#fresh_gmp_var() in
		Format.fprintf fmt "mpz_t %s;@\n" var;
		Format.fprintf fmt "__gmpz_init(%s);@\n" var;
		Format.fprintf fmt "__gmpz_abs(%s, %s);@\n" var x;
		Format.fprintf fmt "__gmpz_clear(%s);@\n" x;
		var
	      end
	    else
	      if builtin_name = "\\min" || builtin_name = "\\max" ||
		builtin_name = "\\sum" || builtin_name = "\\product" ||
		builtin_name = "\\numof" then
		begin
		  match params with
		  | [lower;upper;{term_node=Tlambda([q],t)}] ->
		    self#lambda_and_var fmt li lower upper q t
		  | _ -> assert false
		end
	      else
		assert false
	  | Lreal -> assert false (* TODO: reals *)
	  | _ -> assert false (* unreachable *)
      end

    | Tlambda _ -> assert false (* unreachable *)
    | TDataCons _ -> Sd_options.Self.not_yet_implemented "TDataCons"
    
    | Tif (cond, then_b, else_b) -> (* untested *)
      begin
	match ty with
	| Linteger ->
	  let var = self#fresh_gmp_var() in
	  Format.fprintf fmt "mpz_t %s;@\n" var;
	  let cond' = self#term_and_var fmt cond in
	  Format.fprintf fmt "if (__gmpz_cmp(%s,0) != 0) {@\n" cond';
	  let then_b' = self#term_and_var fmt then_b in
	  Format.fprintf fmt "__gmpz_init_set(%s, %s);@\n" var then_b';
	  Format.fprintf fmt "__gmpz_clear(%s);@\n" then_b';
	  Format.fprintf fmt "}@\n";
	  Format.fprintf fmt "else {@\n";
	  let else_b' = self#term_and_var fmt else_b in
	  Format.fprintf fmt "__gmpz_init_set(%s, %s);@\n" var else_b';
	  Format.fprintf fmt "__gmpz_clear(%s);@\n" else_b';
	  Format.fprintf fmt "}@\n";
	  Format.fprintf fmt "__gmpz_clear(%s);@\n" cond';
	  var
	| Lreal -> assert false (* TODO: reals *)
	| _ -> assert false (* unreachable *)
      end

    
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

    | Tbase_addr _ -> Sd_options.Self.not_yet_implemented "Tbase_addr"
    | Toffset _ -> Sd_options.Self.not_yet_implemented "Toffset"
    | Tblock_length _ -> Sd_options.Self.not_yet_implemented "Tblock_length"
    | Tnull -> "0"

    (* C type -> logic type *)
    | TLogic_coerce (_, t')
    | TCoerceE (t', {term_type=(Linteger|Lreal)}) ->
      begin
	match ty with
	| Linteger ->
	  begin
	    let ty' =
	      match t'.term_type with
	      | Ctype x -> Ctype (Cil.unrollType x)
	      | x -> x
	    in
	    match ty' with
	    | Ctype (TInt((IULongLong|IULong|IUShort|IUInt|IUChar),_)) ->
	      let v = self#term_and_var fmt t' in
	      let var = self#fresh_gmp_var() in
	      Format.fprintf fmt "mpz_t %s;@\n" var;
	      Format.fprintf fmt "__gmpz_init_set_ui(%s, %s);@\n" var v;
	      var
	    | Ctype(TInt _) | Ctype(TEnum _) ->
	      let v = self#term_and_var fmt t' in
	      let var = self#fresh_gmp_var() in
	      Format.fprintf fmt "mpz_t %s;@\n" var;
	      Format.fprintf fmt "__gmpz_init_set_si(%s, %s);@\n" var v;
	      var
	    | _ -> assert false
	  end
	| Lreal -> assert false (* TODO: reals *)
	| _ -> assert false (* unreachable *)
      end

    (* logic type -> C type *)
    | TCoerce (t', ty')
    | TCoerceE (t', {term_type=Ctype ty'}) ->
      begin
	match t'.term_type with
	| Linteger ->
	  let v = self#term_and_var fmt t' in
	  let var = self#fresh_term_var() in
	  Format.fprintf fmt "%a %s;@\n" (self#typ None) ty' var;
	  begin
	    match ty' with
	    | TInt((IULongLong|IULong|IUShort|IUInt|IUChar),_) ->
	      Format.fprintf fmt "%s = __gmpz_get_ui(%s);@\n" var v
	    | TInt _ ->
	      Format.fprintf fmt "%s = __gmpz_get_si(%s);@\n" var v
	    | _ -> assert false
	  end;
	  Format.fprintf fmt "__gmpz_clear(%s);@\n" v;
	  var
	| Lreal -> assert false (* TODO: reals *)
	| _ -> assert false (* unreachable *)
      end

    | TCoerceE _ -> Sd_options.Self.not_yet_implemented "TCoerceE"
    | TUpdate _ -> Sd_options.Self.not_yet_implemented "TUpdate"
    | Ttypeof _ -> Sd_options.Self.not_yet_implemented "Ttypeof"
    | Ttype _ -> Sd_options.Self.not_yet_implemented "Ttype"
    | Tempty_set -> Sd_options.Self.not_yet_implemented "Tempty_set"
    | Tunion _ -> Sd_options.Self.not_yet_implemented "Tunion"
    | Tinter _ -> Sd_options.Self.not_yet_implemented "Tinter"
    | Tcomprehension _ -> Sd_options.Self.not_yet_implemented "Tcomprehension"
    | Trange _ -> assert false (* unreachable *)
    | Tlet _ -> assert false (* unreachable *)
      
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
    | TMem t -> "*" ^ (self#term_and_var fmt t)

  method private term_offset_and_var fmt toffset =
    match toffset with
    | TNoOffset -> ""
    | TField (fi, tof) -> "." ^ fi.fname ^ (self#term_offset_and_var fmt tof)
    | TModel (mi, tof) -> "." ^ mi.mi_name ^ (self#term_offset_and_var fmt tof)
    | TIndex (t, tof) ->
      let t' = self#term_and_var fmt t in
      let v = self#term_offset_and_var fmt tof in
      match t.term_type with
      | Linteger -> "[__gmpz_get_si(" ^ t' ^ ")]" ^ v
      | Lreal -> assert false (* TODO: reals *)
      | _ -> "[" ^ t' ^ "]" ^ v

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
	  let not_translated p =
	    Sd_states.Not_Translated_Predicates.fold_left
	      (fun b e -> b || e = p.ip_id) false
	  in
	  (* TODO: add an option to translate anyway? (deleting the filter) *)
	  let preconds = List.filter not_translated preconds in
	  let do_precond p =
	    let v = self#predicate_and_var fmt (self#subst_pred p.ip_content) in
	    if v <> "1" then (* '1' is for untreated predicates *)
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
      if (self#at_least_one_prop kf behaviors)
	|| (Sd_options.Behavior_Reachability.get()) then
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
	    if post <> [] || (Sd_options.Behavior_Reachability.get()) then
	      begin
		self#bhv_assumes_begin fmt b loc;

		if not (Cil.is_default_behavior b)
		  && (Sd_options.Behavior_Reachability.get()) then
		  begin
		    Format.fprintf fmt
		      "pathcrawler_to_framac(\"@@FC:REACHABLE_BHV:%i\");@\n"
		      bhv_to_reach_cpt;
		    Sd_states.Behavior_Reachability.replace
		      bhv_to_reach_cpt
		      (kf, b, false);
		    bhv_to_reach_cpt <- bhv_to_reach_cpt+1
		  end;

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
    let array_to_ptr x = array_to_ptr (Cil.unrollTypeDeep x) in
    let dig_type = function
      | TPtr(ty,_) | TArray(ty,_,_,_) -> ty
      | ty -> Sd_options.Self.abort "dig_type %a" (self#typ None) ty
    in
    let dig_type x = dig_type (Cil.unrollTypeDeep x) in
    begin
      let iter_counter = ref 0 in
      let lengths = lengths_from_requires kf in

      let do_varinfo v =
	let terms =
	  try Cil_datatype.Varinfo.Hashtbl.find lengths v
	  with Not_found -> []
	in
	Format.fprintf fmt "%a = %s;@\n"
	  (self#typ(Some(fun fmt -> Format.fprintf fmt "old_%s" v.vname)))
	  (array_to_ptr v.vtype)
	  v.vname;
	let rec alloc_aux indices ty = function
	  | h :: t ->
	    let all_indices = List.fold_left concat_indice "" indices in
	    let ty = dig_type ty in
	    let h' = self#term_and_var fmt h in
	    let iterator = "__stady_iter_" ^ (string_of_int !iter_counter) in
	    Format.fprintf fmt "int %s;@\n" iterator;
	    begin
	      match h.term_type with
	      | Linteger ->
		Format.fprintf fmt
		  "old_ptr_%s%s = malloc(__gmpz_get_si(%s)*sizeof(%a));@\n"
		  v.vname all_indices h' (self#typ None) ty;
		Format.fprintf fmt
		  "for (%s = 0; %s < __gmpz_get_si(%s); %s++) {@\n"
		  iterator iterator h' iterator;
		iter_counter := !iter_counter + 1;
		alloc_aux (Sd_utils.append_end indices iterator) ty t;
		Format.fprintf fmt "}@\n"
	      | Lreal -> assert false (* TODO: reals *)
	      | _ ->
		Format.fprintf fmt "old_ptr_%s%s = malloc((%s)*sizeof(%a));@\n"
		  v.vname all_indices h' (self#typ None) ty;
		Format.fprintf fmt "for (%s = 0; %s < %s; %s++) {@\n"
		  iterator iterator h' iterator;
		iter_counter := !iter_counter + 1;
		alloc_aux (Sd_utils.append_end indices iterator) ty t;
		Format.fprintf fmt "}@\n";
		Format.fprintf fmt "__gmpz_clear(%s);@\n" h'
	    end
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
      in

      List.iter do_varinfo visited_globals;
      List.iter do_varinfo (Kernel_function.get_formals kf)
    end;
    dealloc <- (* dealloc variables for \at terms *)
      (try
	 fun fmt ->
	   let iter_counter = ref 0 in
	   let lengths = lengths_from_requires kf in

	   let do_varinfo v =
	     let terms =
	       try Cil_datatype.Varinfo.Hashtbl.find lengths v
	       with Not_found -> []
	     in
	     let rec dealloc_aux indices = function
	       | [] -> ()
	       | _ :: [] ->
		 let all_indices = List.fold_left concat_indice "" indices in
		 Format.fprintf fmt "free(old_ptr_%s%s);@\n" v.vname all_indices
	       | h :: t ->
		 let iterator = "__stady_iter_"^(string_of_int !iter_counter) in
		 Format.fprintf fmt "int %s;@\n" iterator;
		 let h' = self#term_and_var fmt h in
		 let all_indices = List.fold_left concat_indice "" indices in
		 iter_counter := !iter_counter + 1;
		 let indices = Sd_utils.append_end indices iterator in
		 begin
		   match h.term_type with
		   | Linteger ->
		     Format.fprintf fmt
		       "for (%s = 0; %s < __gmpz_get_si(%s); %s++) {@\n"
		       iterator iterator h' iterator;
		     dealloc_aux indices t;
		     Format.fprintf fmt "}@\n";
		     Format.fprintf fmt "__gmpz_clear(%s);@\n" h'
		   | Lreal -> assert false (* TODO: reals *)
		   | _ ->
		     Format.fprintf fmt "for (%s = 0; %s < %s; %s++) {@\n"
		       iterator iterator h' iterator;
		     dealloc_aux indices t;
		     Format.fprintf fmt "}@\n"
		 end;
		 Format.fprintf fmt "free(old_ptr_%s%s);@\n" v.vname all_indices
	     in
	     dealloc_aux [] terms
	   in

	   List.iter do_varinfo visited_globals;
	   List.iter do_varinfo (Kernel_function.get_formals kf)
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
    let begin_loop = ref ([]: (Format.formatter -> unit) list) in
    let end_loop = ref ([]: (Format.formatter -> unit) list) in
    let has_code_annots = List.length (Annotations.code_annot stmt) > 0 in
    let end_contract = ref ([]: (Format.formatter -> unit) list) in
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
	  begin
	    match term.term_type with
	    | Linteger ->
	      end_contract := (fun fmt ->
		Format.fprintf fmt "__gmpz_clear(%s);@\n" term'
	      ) :: !end_contract;
	      Format.fprintf fmt "@[<hv>%a@[<v 2>if (__gmpz_cmp_ui(%s, 0) < 0)"
		(fun fmt -> self#line_directive ~forcefile:false fmt) loc term'
	    | Lreal -> assert false (* TODO: reals *)
	    | _ ->
	      Format.fprintf fmt "@[<hv>%a@[<v 2>if ((%s) < 0)"
		(fun fmt -> self#line_directive ~forcefile:false fmt) loc term'
	  end;
	  Format.fprintf fmt
	    "pathcrawler_assert_exception(\"Variant non positive\",%i);" id;
	  Format.fprintf fmt "@]@]";
	  translated_properties <- prop :: translated_properties;
	  begin_loop :=
	    (fun fmt ->
	      let term' = self#term_and_var fmt term in
	      match
		term.term_type with
		| Linteger ->
		  Format.fprintf fmt "mpz_t old_variant_%i;@\n" id;
		  Format.fprintf fmt "__gmpz_init_set(old_variant_%i, %s);@\n"
		    id term'
		| Lreal -> assert false (* TODO: reals *)
		| _ ->
		  Format.fprintf fmt "int old_variant_%i = %s;@\n" id term'
	    )
	  :: !begin_loop;
	  end_loop :=
	    (fun fmt ->
	      let term' = self#term_and_var fmt term in
	      begin
		match term.term_type with
		| Linteger ->
		  Format.fprintf fmt
		    "@[<hv>%a@[<v 2>if (__gmpz_cmp_ui(old_variant_%i,0) < 0)"
		    (fun fmt -> self#line_directive ~forcefile:false fmt) loc id
		| Lreal -> assert false (* TODO: reals *)
		| _ ->
		  Format.fprintf fmt "@[<hv>%a@[<v 2>if ((old_variant_%i) < 0)"
		    (fun fmt -> self#line_directive ~forcefile:false fmt) loc id
	      end;
	      Format.fprintf fmt
		"pathcrawler_assert_exception(\"Variant non positive\",%i);"
		id;
	      Format.fprintf fmt "@]@]";
	      
	      begin
		match term.term_type with
		| Linteger ->
		  Format.fprintf fmt
		    "@[<hv>%a@[<v 2>if (__gmpz_cmp(%s, old_variant_%i) >= 0)"
		    (fun fmt -> self#line_directive ~forcefile:false fmt) loc
		    term' id
		| Lreal -> assert false (* TODO: reals *)
		| _ ->
		  Format.fprintf fmt
		    "@[<hv>%a@[<v 2>if ((%s) >= old_variant_%i)"
		    (fun fmt -> self#line_directive ~forcefile:false fmt) loc
		    term' id
	      end;
	      Format.fprintf fmt
		"pathcrawler_assert_exception(\"Variant non decreasing\",%i);"
		id;
	      Format.fprintf fmt "@]@]";
	      begin
		match term.term_type with
		| Linteger ->
		  Format.fprintf fmt "__gmpz_clear(old_variant_%i);@\n" id
		| Lreal -> assert false (* TODO: reals *)
		| _ -> ()
	      end;
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

  method! stmtkind (next: stmt) fmt s =
    let cur_stmt = Extlib.the self#current_stmt in
    let has_added_reachable_stmt =
      if List.mem cur_stmt.sid stmts_to_reach then
	(Format.fprintf fmt
	   "{ pathcrawler_to_framac(\"@@FC:REACHABLE_STMT:%i\");@\n"
	   cur_stmt.sid;
	 true)
      else false
    in
    let kf = Kernel_function.find_englobing_kf cur_stmt in
    begin
      match s with
      | If(_exp,b1,b2,_loc) ->
	begin
      	  match b1.bstmts with
      	  | first_stmt :: _ ->
      	    Sd_options.Self.debug ~dkey:Sd_options.dkey_reach
	      "stmt %i to reach" first_stmt.sid;
	    Sd_states.Unreachable_Stmts.replace first_stmt.sid (first_stmt, kf);
      	    stmts_to_reach <- first_stmt.sid :: stmts_to_reach
      	  | _ -> ()
	end;
	begin
      	  match b2.bstmts with
      	  | first_stmt :: _ ->
	    Sd_options.Self.debug ~dkey:Sd_options.dkey_reach
	      "stmt %i to reach" first_stmt.sid;
	    Sd_states.Unreachable_Stmts.replace first_stmt.sid (first_stmt, kf);
      	    stmts_to_reach <- first_stmt.sid :: stmts_to_reach
      	  | _ -> ()
	end;
	super#stmtkind next fmt s
      | _ -> super#stmtkind next fmt s
    end;
    if has_added_reachable_stmt then
      Format.fprintf fmt " }@\n"

  method! global fmt g =
    if first_global then
      begin
	Format.fprintf fmt "#include <gmp.h>@\n";
	Format.fprintf fmt
	  "extern int pathcrawler_assert_exception(char*,int);@\n";
	Format.fprintf fmt "extern int pathcrawler_dimension(void*);@\n";
	Format.fprintf fmt "extern void pathcrawler_to_framac(char*);@\n";
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
    | GVar (vi, _, _) ->
      visited_globals <- vi :: visited_globals;
      super#global fmt g
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
    let var = self#fresh_pred_var() in
    let guards, vars = Sd_utils.compute_guards [] logic_vars hyps in
    if vars <> [] then
      failwith "Unguarded variables in quantification!";
    let t1,r1,lv,r2,t2 = List.hd guards in
    let iter = lv.lv_name in
    Format.fprintf fmt "int %s = %i;@\n" var (if forall then 1 else 0);
    Format.fprintf fmt "{@\n";
    begin
      match t1.term_type with
      | Linteger ->
	begin
	  match t2.term_type with
	  | Linteger ->
	    Format.fprintf fmt "mpz_t %s;@\n" iter;
	    let t1' = self#term_and_var fmt t1 in
	    let t2' = self#term_and_var fmt t2 in
	    Format.fprintf fmt "__gmpz_init_set(%s, %s);@\n" iter t1';
	    if r1 = Rlt then
	      Format.fprintf fmt "__gmpz_add_ui(%s, %s, 1);@\n" iter iter;
	    Format.fprintf fmt "for (; __gmpz_cmp(%s, %s) %a 0 && %s %s;) {@\n"
	      iter t2' self#relation r2 (if forall then "" else "!") var;
	    let goal_var = self#predicate_named_and_var fmt goal in 
	    Format.fprintf fmt "%s = %s;@\n" var goal_var;
	    Format.fprintf fmt "__gmpz_add_ui(%s, %s, 1);@\n" iter iter;
	    Format.fprintf fmt "}@\n";
	    Format.fprintf fmt "__gmpz_clear(%s);@\n" iter;
	    Format.fprintf fmt "__gmpz_clear(%s);@\n" t1';
	    Format.fprintf fmt "__gmpz_clear(%s);@\n" t2'
	  | Lreal -> assert false (* TODO: reals *)
	  | _ ->
	    Format.fprintf fmt "mpz_t %s;@\n" iter;
	    let t1' = self#term_and_var fmt t1 in
	    let t2' = self#term_and_var fmt t2 in
	    Format.fprintf fmt "__gmpz_init_set(%s, %s);@\n" iter t1';
	    if r1 = Rlt then
	      Format.fprintf fmt "__gmpz_add_ui(%s, %s, 1);@\n" iter iter;
	    Format.fprintf fmt
	      "for (; __gmpz_cmp_si(%s, %s) %a 0 && %s %s;) {@\n"
	      iter t2' self#relation r2 (if forall then "" else "!") var;
	    let goal_var = self#predicate_named_and_var fmt goal in 
	    Format.fprintf fmt "%s = %s;@\n" var goal_var;
	    Format.fprintf fmt "__gmpz_add_ui(%s, %s, 1);@\n" iter iter;
	    Format.fprintf fmt "}@\n";
	    Format.fprintf fmt "__gmpz_clear(%s);@\n" iter;
	    Format.fprintf fmt "__gmpz_clear(%s);@\n" t1'
	end
      | Lreal -> assert false (* TODO: reals *)
      | _ ->
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
	Format.fprintf fmt "}@\n"
    end;
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
      let loc = term.term_loc in
      let pointer, offset =
	match term.term_node with
	| TLval _ -> term, Cil.lzero ~loc ()
	| TBinOp ((PlusPI|IndexPI),x,{term_node = Trange(_,Some y)}) -> x,y
	| TBinOp ((PlusPI|IndexPI),x,y) -> x,y
	| TBinOp (MinusPI,x,y) ->
	  let einfo = {exp_type=y.term_type; exp_name=[]} in
	  x, Cil.term_of_exp_info loc (TUnOp(Neg,y)) einfo
	| _ -> Sd_utils.error_term term
      in
      let x' = self#term_and_var fmt pointer in
      let y' = self#term_and_var fmt offset in
      begin
	match offset.term_type with
	| Linteger ->
	  let var = self#fresh_pred_var() in
	  Format.fprintf fmt "int %s = __gmpz_cmp_ui(%s, 0) >= 0 && \
 __gmpz_cmp_ui(%s, pathcrawler_dimension(%s)) < 0;@\n" var y' y' x';
	  Format.fprintf fmt "__gmpz_clear(%s);@\n" y';
	  var
	| Lreal -> assert false (* unreachable *)
	| Ctype (TInt _) -> Format.fprintf Format.str_formatter
	  "(%s >= 0 && pathcrawler_dimension(%s) > %s)"
	  y' x' y';
	  Format.flush_str_formatter()
	| _ -> assert false (* unreachable *)
      end
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
      let var = self#fresh_pred_var() in
      let pred1_var = self#predicate_named_and_var fmt pred1 in
      Format.fprintf fmt "int %s = %s;@\n" var pred1_var;
      Format.fprintf fmt "if (%s) {@\n" var;
      let pred2_var = self#predicate_named_and_var fmt pred2 in
      Format.fprintf fmt "%s = %s;@\n" var pred2_var;
      Format.fprintf fmt "}@\n";
      var
    | Por(pred1,pred2) ->
      let var = self#fresh_pred_var() in
      let pred1_var = self#predicate_named_and_var fmt pred1 in
      Format.fprintf fmt "int %s = %s;@\n" var pred1_var;
      Format.fprintf fmt "if (!%s) {@\n" var;
      let pred2_var = self#predicate_named_and_var fmt pred2 in
      Format.fprintf fmt "%s = %s;@\n" var pred2_var;
      Format.fprintf fmt "}@\n";
      var
    | Pimplies(pred1,pred2) ->
      let var = self#fresh_pred_var() in
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
    | Pif (t,pred1,pred2) -> (* untested *)
      begin
	let term_var = self#term_and_var fmt t in
	let res_var = self#fresh_pred_var() in
	Format.fprintf fmt "int %s;@\n" res_var;
	let f fmt =
	  Format.fprintf fmt "if(%s) {@\n" term_var;
	  let pred1_var = self#predicate_named_and_var fmt pred1 in
	  Format.fprintf fmt "%s = %s;@\n" res_var pred1_var;
	  Format.fprintf fmt "} else {@\n";
	  let pred2_var = self#predicate_named_and_var fmt pred2 in
	  Format.fprintf fmt "%s = %s;@\n" res_var pred2_var;
	  Format.fprintf fmt "}@\n";
	  res_var
	in
	match t.term_type with
	| Linteger ->
	  Format.fprintf fmt "if(__gmpz_cmp_si(%s,0) != 0) {@\n" term_var;
	  let pred1_var = self#predicate_named_and_var fmt pred1 in
	  Format.fprintf fmt "%s = %s;@\n" res_var pred1_var;
	  Format.fprintf fmt "} else {@\n";
	  let pred2_var = self#predicate_named_and_var fmt pred2 in
	  Format.fprintf fmt "%s = %s;@\n" res_var pred2_var;
	  Format.fprintf fmt "}@\n";
	  Format.fprintf fmt "__gmpz_clear(%s);@\n" term_var;
	  res_var
	| Lreal -> assert false (* unreachable *)
	| Ctype (TInt _) -> f fmt
	| Ltype (lt,_) when lt.lt_name = Utf8_logic.boolean -> f fmt
	| _ -> assert false (* unreachable *)
      end

    | Prel(rel,t1,t2) ->
      begin
	match t1.term_type, t2.term_type with
	| Linteger, Linteger ->
	  let var = self#fresh_pred_var() in
	  let t1' = self#term_and_var fmt t1 in
	  let t2' = self#term_and_var fmt t2 in
	  Format.fprintf fmt "int %s = __gmpz_cmp(%s, %s) %a 0;@\n" var t1' t2'
	    self#relation rel;
	  Format.fprintf fmt "__gmpz_clear(%s);@\n" t1';
	  Format.fprintf fmt "__gmpz_clear(%s);@\n" t2';
	  var
	| Linteger, Ctype (TInt((IULongLong|IULong|IUShort|IUInt|IUChar),_)) ->
	  let var = self#fresh_pred_var() in
	  let t1' = self#term_and_var fmt t1 in
	  let t2' = self#term_and_var fmt t2 in
	  Format.fprintf fmt
	    "int %s = __gmpz_cmp_ui(%s, %s) %a 0;@\n" var t1' t2'
	    self#relation rel;
	  Format.fprintf fmt "__gmpz_clear(%s);@\n" t1';
	  var
	| Linteger, Ctype (TInt _) ->
	  let var = self#fresh_pred_var() in
	  let t1' = self#term_and_var fmt t1 in
	  let t2' = self#term_and_var fmt t2 in
	  Format.fprintf fmt
	    "int %s = __gmpz_cmp_si(%s, %s) %a 0;@\n" var t1' t2'
	    self#relation rel;
	  Format.fprintf fmt "__gmpz_clear(%s);@\n" t1';
	  var
	| Lreal, Lreal -> assert false (* TODO: reals *)
	| Ctype (TInt((IULongLong|IULong|IUShort|IUInt|IUChar),_)), Linteger ->
	  let var = self#fresh_pred_var() in
	  let t1' = self#term_and_var fmt t1 in
	  let t2' = self#term_and_var fmt t2 in
	  let var' = self#fresh_gmp_var() in
	  Format.fprintf fmt "mpz_t %s;@\n" var';
	  Format.fprintf fmt "__gmpz_init_set_ui(%s, %s);@\n" var' t1';
	  Format.fprintf fmt "int %s = __gmpz_cmp(%s, %s) %a 0;@\n"
	    var var' t2' self#relation rel;
	  Format.fprintf fmt "__gmpz_clear(%s);@\n" t2';
	  Format.fprintf fmt "__gmpz_clear(%s);@\n" var';
	  var
	| Ctype (TInt _), Linteger ->
	  let var = self#fresh_pred_var() in
	  let t1' = self#term_and_var fmt t1 in
	  let t2' = self#term_and_var fmt t2 in
	  let var' = self#fresh_gmp_var() in
	  Format.fprintf fmt "mpz_t %s;@\n" var';
	  Format.fprintf fmt "__gmpz_init_set_si(%s, %s);@\n" var' t1';
	  Format.fprintf fmt "int %s = __gmpz_cmp(%s, %s) %a 0;@\n"
	    var var' t2' self#relation rel;
	  Format.fprintf fmt "__gmpz_clear(%s);@\n" t2';
	  Format.fprintf fmt "__gmpz_clear(%s);@\n" var';
	  var
	| _ ->
          let t1' = self#term_and_var fmt t1 in
          let t2' = self#term_and_var fmt t2 in
	  Format.fprintf Format.str_formatter "(%s %a %s)"
	    t1' self#relation rel t2';
	  Format.flush_str_formatter()
      end
      
    | Pat(p, LogicLabel(_,stringlabel)) when stringlabel = "Here" ->
      self#predicate_named_and_var fmt p
    | Pat (p,_) ->
      Sd_options.Self.warning "%a unsupported!" Printer.pp_predicate pred;
      self#predicate_named_and_var fmt p
    | _ ->
      Sd_options.Self.warning "%a unsupported" Printer.pp_predicate pred;
      "1"
(* end of pred_and_var *)
end (* end of printer class *)
