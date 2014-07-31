
open Cil_types


let debug_builtins = Kernel.register_category "printer:builtins"

let print_var v =
  not (Cil.is_unused_builtin v) || Kernel.is_debug_key_enabled debug_builtins


type label =
| BegStmt of int
| EndStmt of int
| BegFunc of string
| EndFunc of string
| BegIter of int
| EndIter of int

let pp_label fmt = function
  | BegStmt s -> Format.fprintf fmt "BegStmt %i" s
  | EndStmt s -> Format.fprintf fmt "EndStmt %i" s
  | BegFunc s -> Format.fprintf fmt "BegFunc %s" s
  | EndFunc s -> Format.fprintf fmt "EndFunc %s" s
  | BegIter s -> Format.fprintf fmt "BegIter %i" s
  | EndIter s -> Format.fprintf fmt "EndIter %i" s

type fresh_gmp_var =
| Fresh_gmp_var of int (* uid *)
| My_gmp_var of string

type declared_gmp_var =
| Declared_gmp_var of fresh_gmp_var

type initialized_gmp_var =
| Initialized_gmp_var of declared_gmp_var

and gmp_expr = initialized_gmp_var

and ctype_expr = (* distinguer type pointeur/int *)
| Fresh_ctype_var of int (* uid *) * typ
| My_ctype_var of typ * string (* when its name is predefined *)
| Zero | One
| Cst of string
| Gmp_get_ui of gmp_expr
| Gmp_get_si of gmp_expr
| Unop of unop * ctype_expr
| Binop of binop * ctype_expr * ctype_expr
| Pc_dim of ctype_expr
| Malloc of ctype_expr
| Cast of typ * ctype_expr
| Sizeof of typ
| Deref of ctype_expr
| Index of ctype_expr * ctype_expr
| Field of ctype_expr * string
| Of_pred of pred_expr

and pred_expr =
| Fresh_pred_var of int (* uid *)
| True | False
| Cmp of relation * ctype_expr * ctype_expr
| Gmp_cmp of binop * gmp_expr * gmp_expr
| Gmp_cmp_ui of binop * gmp_expr * ctype_expr
| Gmp_cmp_si of binop * gmp_expr * ctype_expr
| Gmp_cmpr of relation * gmp_expr * gmp_expr
| Gmp_cmpr_ui of relation * gmp_expr * ctype_expr
| Gmp_cmpr_si of relation * gmp_expr * ctype_expr
| Lnot of pred_expr
| Land of pred_expr * pred_expr
| Lor of pred_expr * pred_expr

and fragment =
| Gmp_fragment of gmp_expr
| Ctype_fragment of ctype_expr

and instruction =
| Affect of ctype_expr * ctype_expr
| Affect_pred of pred_expr * pred_expr
| Free of ctype_expr
| Pc_to_framac of string
| Pc_exn of string * int
| Ret of ctype_expr
| Gmp_clear of gmp_expr
| Gmp_init of declared_gmp_var
| Gmp_init_set of declared_gmp_var * gmp_expr
| Gmp_init_set_ui of declared_gmp_var * ctype_expr
| Gmp_init_set_si of declared_gmp_var * ctype_expr
| Gmp_init_set_str of declared_gmp_var * string
| Gmp_set of gmp_expr * gmp_expr
| Gmp_abs of gmp_expr * gmp_expr
| Gmp_ui_sub of gmp_expr * ctype_expr * gmp_expr
| Gmp_binop of binop * gmp_expr * gmp_expr * gmp_expr
| Gmp_binop_ui of binop * gmp_expr * gmp_expr * ctype_expr
| Gmp_binop_si of binop * gmp_expr * gmp_expr * ctype_expr

type insertion =
| Instru of instruction
| Decl_gmp_var of fresh_gmp_var
| Decl_ctype_var of ctype_expr
| Decl_pred_var of pred_expr
| If of pred_expr * insertion list * insertion list
| For of instruction option * pred_expr option * instruction option *
    insertion list
| Block of insertion list


class gather_insertions props = object(self)
  inherit Visitor.frama_c_inplace as super

  val insertions : (label, insertion Queue.t) Hashtbl.t = Hashtbl.create 64
  val mutable current_label : label option = None
  val mutable result_varinfo = None
  val mutable current_function = None
  val mutable in_old_term = false
  val mutable in_old_ptr = false
  val mutable bhv_to_reach_cpt = 0
  val mutable visited_globals = []
  val mutable last_gmp_var_id = -1
  val mutable last_ctype_var_id = -1
  val mutable last_pred_var_id = -1

  (* list of (stmtkind * stmt) used for testing reachibility of some stmts *)
  val mutable stmts_to_reach = []

  (* we can only modify the property_status of the properties that have really
     been translated into pathcrawler_assert_exception *)
  val mutable translated_properties = []

  method get_insertions () =
    insertions

  method private insert str =
    let label = Extlib.the current_label in
    try
      Queue.add str (Hashtbl.find insertions label)
    with Not_found ->
      let q = Queue.create() in
      Queue.add str q;
      Hashtbl.add insertions label q

  method private fresh_gmp_var() =
    last_gmp_var_id <- last_gmp_var_id + 1;
    Fresh_gmp_var last_gmp_var_id

  method private decl_gmp_var var =
    Decl_gmp_var var, Declared_gmp_var var

  method private init_gmp_var var =
    Instru(Gmp_init var), Initialized_gmp_var var

  method private init_set_gmp_var var v =
    Instru(Gmp_init_set (var, v)), Initialized_gmp_var var

  method private init_set_si_gmp_var var v =
    Instru(Gmp_init_set_si (var, v)), Initialized_gmp_var var

  method private init_set_ui_gmp_var var v =
    Instru(Gmp_init_set_ui (var, v)), Initialized_gmp_var var

  method private init_set_str_gmp_var var v =
    Instru(Gmp_init_set_str (var, v)), Initialized_gmp_var var

  method private fresh_ctype_var ty =
    last_ctype_var_id <- last_ctype_var_id + 1;
    Fresh_ctype_var (last_ctype_var_id, ty)

  method private fresh_pred_var() =
    last_pred_var_id <- last_pred_var_id + 1;
    Fresh_pred_var last_pred_var_id

  (* unmodified *)
  method private in_current_function vi =
    assert (current_function = None);
    current_function <- Some vi

  (* unmodified *)
  method private out_current_function =
    assert (current_function <> None);
    current_function <- None

  (* getter *)
  method translated_properties() = Sd_utils.no_repeat translated_properties

  method private logic_var v =
    let ret =
      match current_function with
      | Some _ when in_old_term ->
	let prefix =
	  match v.lv_type with
	  | Ctype ty
	      when (Cil.isPointerType ty || Cil.isArrayType ty) && in_old_ptr ->
	    "old_ptr"
	  | _ -> "old"
	in
	begin
	  match v.lv_origin with
	  | Some _ -> prefix ^ "_" ^ v.lv_name
	  | None -> v.lv_name
	end
      | _ -> v.lv_name
    in
    match v.lv_type with
    | Linteger ->
      Gmp_fragment (Initialized_gmp_var(Declared_gmp_var(My_gmp_var ret)))
    | Lreal -> assert false (* TODO: reals *)
    | Ctype ty -> Ctype_fragment (My_ctype_var (ty, ret))
    | _ -> assert false

  method private term t : insertion list * fragment =
    self#term_node t

  method private gmp_fragment = function
  | Gmp_fragment x -> x
  | Ctype_fragment _ -> assert false

  method private ctype_fragment = function
  | Ctype_fragment x -> x
  | Gmp_fragment _ -> assert false

  method private lambda li lower upper q t =
    let builtin_name = li.l_var_info.lv_name in
    let init_val = match builtin_name with
      | s when s = "\\sum" -> Zero
      | s when s = "\\product" -> One
      | s when s = "\\numof" -> Zero
      | _ -> assert false (* unreachable *)
    in
    let fresh_var = self#fresh_gmp_var() in
    let insert_0, decl_var = self#decl_gmp_var fresh_var in
    let insert_1, init_var = self#init_set_si_gmp_var decl_var init_val in
    let inserts_block =
      match lower.term_type with
      | Linteger ->
	begin
	  match upper.term_type with
	  | Linteger ->
	    let inserts_3, low = self#term lower in
	    let inserts_4, up = self#term upper in
	    let low = self#gmp_fragment low in
	    let up = self#gmp_fragment up in
	    let fresh_iter = My_gmp_var q.lv_name in
	    let insert_5, decl_iter = self#decl_gmp_var fresh_iter in
	    let insert_6, init_iter = self#init_set_gmp_var decl_iter low in
	    let ins_b_0, lambda_term = self#term t in
	    let ins_b_1 =
	      match builtin_name with
	      | s when s = "\\sum" ->
		Instru(Gmp_binop(PlusA, init_var, init_var,
				 self#gmp_fragment lambda_term));
	      | s when s = "\\product" ->
		Instru(Gmp_binop(Mult, init_var, init_var,
				 self#gmp_fragment lambda_term));
	      | s when s = "\\numof" ->
		(* lambda_term is of type:
		   Ltype (lt,_) when lt.lt_name = Utf8_logic.boolean *)
		let cond = Cmp(Rneq,self#ctype_fragment lambda_term,Zero) in
		let instr = Instru(Gmp_binop_ui(PlusA,init_var,init_var,One)) in
		If(cond, [instr], [])
	      | _ -> assert false
	    in
	    let ins_b_2 = Instru(Gmp_binop_ui(PlusA,init_iter,init_iter,One)) in
	    let ins_b = ins_b_0 @ [ins_b_1; ins_b_2] in
	    let ins_b =
	      if builtin_name <> "\\numof" then
		ins_b @ [(Instru(Gmp_clear(self#gmp_fragment lambda_term)))]
	      else
		ins_b
	    in
	    let cond = Gmp_cmp(Le,init_iter,up) in
	    let insert_7 = For(None, Some cond, None, ins_b) in
	    let insert_8 = Instru(Gmp_clear init_iter) in
	    let insert_9 = Instru(Gmp_clear low) in
	    let insert_10 = Instru(Gmp_clear up) in
	    inserts_3 @ inserts_4
	    @ [insert_5; insert_6; insert_7; insert_8; insert_9; insert_10]
	  | Lreal -> assert false (* unreachable *)
	  | _ -> assert false (* unreachable ? *)
	 end
      | Lreal -> assert false (* unreachable *)
      | _ -> assert false (* unreachable ? *)
    in
    let insert_2 = Block inserts_block in
    [insert_0; insert_1; insert_2], Gmp_fragment init_var

  method private term_node t =
    let ty = match t.term_type with
      | Ctype c -> Ctype (Cil.unrollType c)
      | x -> x
    in
    match t.term_node with

    | TConst _ ->
      begin
	match ty with
	| Linteger ->
	  let fresh_var = self#fresh_gmp_var() in
	  let insert_0, decl_var = self#decl_gmp_var fresh_var in
	  let str = Pretty_utils.sfprintf "%a" Printer.pp_term t in
	  let insert_1, init_var = self#init_set_str_gmp_var decl_var str in
	  [insert_0; insert_1], Gmp_fragment init_var
	| Lreal -> assert false (* TODO: reals *)
	| _ ->
	  [], Ctype_fragment(Cst(Pretty_utils.sfprintf "%a" Printer.pp_term t))
      end

    | TLval tlval ->
      begin
	match ty with
	| Linteger ->
	  let fresh_var = self#fresh_gmp_var() in
	  let inserts_0, t' = self#tlval tlval in
	  let t' = self#gmp_fragment t' in
	  let insert_1, decl_var = self#decl_gmp_var fresh_var in
	  let insert_2, init_var = self#init_set_gmp_var decl_var t' in
	  inserts_0 @ [insert_1; insert_2], Gmp_fragment init_var
	| Lreal -> assert false (* TODO: reals *)
	| _ -> self#tlval tlval
      end

    | TSizeOf _
    | TSizeOfE _
    | TSizeOfStr _
    | TAlignOf _
    | TAlignOfE _ ->
      assert false (* TODO ? *)

    | TUnOp(op, t') ->
      begin
	match ty with
	| Linteger ->
	  assert(op = Neg);
	  let inserts_0, x = self#term t' in
	  let fresh_var = self#fresh_gmp_var() in
	  let insert_1, decl_var = self#decl_gmp_var fresh_var in
	  let insert_2, init_var = self#init_gmp_var decl_var in
	  let inserts_3 =
	    match t'.term_type with
	    | Linteger ->
	      [Instru(Gmp_ui_sub(init_var,Zero,self#gmp_fragment x));
	       Instru(Gmp_clear(self#gmp_fragment x))]
	    | Lreal -> assert false (* unreachable *)
	    | Ctype ty' ->
	      let fresh_var' = self#fresh_gmp_var() in
	      let insert_0', decl_var' = self#decl_gmp_var fresh_var' in
	      let insert_1', init_var' =
		if Cil.isUnsignedInteger ty' then
		  self#init_set_ui_gmp_var decl_var' (self#ctype_fragment x)
		else if Cil.isSignedInteger ty' then
		  self#init_set_si_gmp_var decl_var' (self#ctype_fragment x)
		else
		  assert false
	      in
	      let insert_2' = Instru(Gmp_ui_sub(init_var', Zero, init_var')) in
	      let insert_3' = Instru(Gmp_clear init_var') in
	      [insert_0'; insert_1'; insert_2'; insert_3']
	    | _ -> assert false (* unreachable *)
	  in
	  inserts_0 @ [insert_1; insert_2] @ inserts_3, Gmp_fragment init_var
	| Lreal -> assert false (* TODO: reals *)
	| _ ->
	  let inserts, x = self#term t' in
	  inserts, Ctype_fragment (Unop(op, self#ctype_fragment x))
      end

    | TBinOp((IndexPI|PlusPI|MinusPI) as op, t1, t2) ->
      begin
	match t2.term_type with
	| Linteger ->
	  let inserts_0, x = self#term t1 in
	  let x = self#ctype_fragment x in
	  let inserts_1, y = self#term t2 in
	  let y = self#gmp_fragment y in
	  let var = self#fresh_ctype_var Cil.intType in
	  let insert_2 = Decl_ctype_var var in
	  let insert_3 = Instru(Affect(var, Gmp_get_si y)) in
	  let insert_4 = Instru(Gmp_clear y) in
	  inserts_0 @ inserts_1 @ [insert_2; insert_3; insert_4],
	  Ctype_fragment (Binop(op, x, var))
	| Lreal -> assert false (* unreachable *)
	| _ ->
	  let inserts_0, x = self#term t1 in
	  let x = self#ctype_fragment x in
	  let inserts_1, y = self#term t2 in
	  let y = self#ctype_fragment y in
	  inserts_0 @ inserts_1, Ctype_fragment (Binop(op, x, y))
      end

    | TBinOp(op, t1, t2) ->
      begin
	match ty with
	| Linteger ->
	  let inserts_0, x = self#term t1 in
	  let inserts_1, y = self#term t2 in
	  let fresh_var = self#fresh_gmp_var() in
	  let insert_2, decl_var = self#decl_gmp_var fresh_var in
	  let insert_3, init_var = self#init_gmp_var decl_var in
	  begin
	    match t1.term_type, t2.term_type with
	    | Linteger, Linteger ->
	      let x = self#gmp_fragment x and y = self#gmp_fragment y in
	      inserts_0 @ inserts_1 @ [insert_2; insert_3]
	      @ [Instru(Gmp_binop(op, init_var, x, y));
		 Instru(Gmp_clear x); Instru(Gmp_clear y)],
	      Gmp_fragment init_var
	    | Linteger, Ctype ty' when Cil.isUnsignedInteger ty' ->
	      let x = self#gmp_fragment x and y = self#ctype_fragment y in
	      inserts_0 @ inserts_1 @ [insert_2; insert_3]
	      @ [Instru(Gmp_binop_ui(op, init_var, x, y)); Instru(Gmp_clear x)],
	      Gmp_fragment init_var
	    | Linteger, Ctype ty' when Cil.isSignedInteger ty' ->
	      let x = self#gmp_fragment x and y = self#ctype_fragment y in
	      inserts_0 @ inserts_1 @ [insert_2; insert_3]
	      @ [Instru(Gmp_binop_si(op, init_var, x, y)); Instru(Gmp_clear x)],
	      Gmp_fragment init_var
	    | Ctype ty', Linteger when Cil.isUnsignedInteger ty' ->
	      if op = PlusA || op = Mult then
		let x = self#ctype_fragment x and y = self#gmp_fragment y in
		inserts_0 @ inserts_1 @ [insert_2; insert_3]
		@ [Instru(Gmp_binop_ui(op,init_var,y,x)); Instru(Gmp_clear y)],
		Gmp_fragment init_var
	      else
		assert false (* TODO *)
	    | Ctype ty', Linteger when Cil.isSignedInteger ty' ->
	      if op = PlusA || op = Mult then
		let x = self#ctype_fragment x and y = self#gmp_fragment y in
		inserts_0 @ inserts_1 @ [insert_2; insert_3]
		@ [Instru(Gmp_binop_si(op, init_var,y,x)); Instru(Gmp_clear y)],
		Gmp_fragment init_var
	      else
		assert false (* TODO *)
	    | Ctype(TInt _), Ctype(TInt _) ->
	      let fresh_var1 = self#fresh_gmp_var() in
	      let insert_4, decl_var1 = self#decl_gmp_var fresh_var1 in
	      let fresh_var2 = self#fresh_gmp_var() in
	      let insert_5, decl_var2 = self#decl_gmp_var fresh_var2 in
	      let insert_6, init_var1 =
		self#init_set_si_gmp_var decl_var1 (self#ctype_fragment x) in
	      let insert_7, init_var2 =
		self#init_set_si_gmp_var decl_var2 (self#ctype_fragment y) in
	      inserts_0 @ inserts_1
	      @	[insert_2; insert_3; insert_4; insert_5; insert_6; insert_7;
		 Instru(Gmp_binop(op,init_var,init_var1,init_var2));
		 Instru(Gmp_clear init_var1);
		 Instru(Gmp_clear init_var2)],
	      Gmp_fragment init_var
	    | _ -> assert false
	  end
	| Lreal -> assert false (* TODO: reals *)
	| Ltype (lt,_) when lt.lt_name = Utf8_logic.boolean ->
	  begin
	    match t1.term_type, t2.term_type with
	    | Linteger, Linteger ->
	      let var = self#fresh_ctype_var Cil.intType in
	      let inserts_0, x = self#term t1 in
	      let inserts_1, y = self#term t2 in
	      let insert_2 = Decl_ctype_var var in
	      let pred = Gmp_cmp(op, self#gmp_fragment x,self#gmp_fragment y) in
	      let insert_3 = Instru(Affect(var, Of_pred pred)) in
	      let insert_4 = Instru(Gmp_clear(self#gmp_fragment x)) in
	      let insert_5 = Instru(Gmp_clear(self#gmp_fragment y)) in
	      inserts_0 @ inserts_1 @ [insert_2; insert_3; insert_4; insert_5],
	      Ctype_fragment var
	    | _ ->
	      let inserts_0, x = self#term t1 in
	      let inserts_1, y = self#term t2 in
	      let x = self#ctype_fragment x and y = self#ctype_fragment y in
	      inserts_0 @ inserts_1, Ctype_fragment (Binop(op, x, y))
	  end
	| _ -> assert false (* unreachable ? *)
      end

    | TCastE (ty', t') ->
      begin
	match t'.term_type with (* source type *)
	| Linteger ->
	  let inserts_0, v = self#term t' in
	  let v = self#gmp_fragment v in
	  let var = self#fresh_ctype_var ty' in
	  let insert_1 = Decl_ctype_var var in
	  let value =
	    match ty with (* dest type *)
	    | Ctype x when Cil.isUnsignedInteger x -> Gmp_get_ui v
	    | Ctype x when Cil.isSignedInteger x -> Gmp_get_si v
	    | _ -> assert false (* unreachable *)
	  in
	  let insert_2 = Instru(Affect(var, value)) in
	  let insert_3 = Instru(Gmp_clear v) in
	  inserts_0 @ [insert_1; insert_2; insert_3], Ctype_fragment var
	| Lreal -> assert false (* reals *)
	| Ctype _ ->
	  let inserts_0, v = self#term t' in
	  inserts_0, Ctype_fragment (Cast (ty', self#ctype_fragment v))
	| _ -> assert false (* unreachable *)
      end

    | TAddrOf _
    | TStartOf _ ->
      assert false (* TODO ? *)

    | Tapp (li, _ (* already substituted *), params) ->
      let builtin_name = li.l_var_info.lv_name in
      begin
	match ty with
	| Linteger ->
	  if builtin_name = "\\abs" then
	    begin
	      let param = List.hd params in
	      assert (List.tl params = []);
	      let inserts_0, x = self#term param in
	      let x = self#gmp_fragment x in
	      let fresh_var = self#fresh_gmp_var() in
	      let insert_1, decl_var = self#decl_gmp_var fresh_var in
	      let insert_2, init_var = self#init_gmp_var decl_var in
	      let insert_3 = Instru(Gmp_abs(init_var, x)) in
	      let insert_4 = Instru(Gmp_clear x) in
	      inserts_0 @ [insert_1; insert_2; insert_3; insert_4],
	      Gmp_fragment init_var
	    end
	  else
	    if builtin_name = "\\min" || builtin_name = "\\max" ||
	      builtin_name = "\\sum" || builtin_name = "\\product" ||
	      builtin_name = "\\numof" then
	      match params with
	      | [l;u;{term_node=Tlambda([q],t)}] -> self#lambda li l u q t
	      | _ -> assert false
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
	  let fresh_var = self#fresh_gmp_var() in
	  let insert_0, decl_var = self#decl_gmp_var fresh_var in
	  let insert_1, init_var = self#init_gmp_var decl_var in
	  let inserts_2, cond' = self#term cond in
	  let cond' = self#gmp_fragment cond' in
	  let cond'' = Gmp_cmp_si(Ne, cond', Zero) in
	  let inserts_then =
	    let inserts_then_0, then_b' = self#term then_b in
	    let then_b' = self#gmp_fragment then_b' in
	    inserts_then_0
	    @ [Instru(Gmp_set(init_var, then_b')); Instru(Gmp_clear then_b')]
	  in
	  let inserts_else =
	    let inserts_else_0, else_b' = self#term else_b in
	    let else_b' = self#gmp_fragment else_b' in
	    inserts_else_0
	    @ [Instru(Gmp_set(init_var, else_b')); Instru(Gmp_clear else_b')]
	  in
	  let insert_3 = If(cond'', inserts_then, inserts_else) in
	  let insert_4 = Instru(Gmp_clear cond') in
	  [insert_0; insert_1] @ inserts_2 @ [insert_3; insert_4],
	  Gmp_fragment init_var
	| Lreal -> assert false (* TODO: reals *)
	| _ -> assert false (* unreachable *)
      end
    
    | Tat(_, StmtLabel _) ->
      if current_function <> None then
	Sd_options.Self.warning "%a unsupported" Printer.pp_term t;
      assert false (* TODO ? *)

    | Tat(term,LogicLabel(_,stringlabel)) ->
      if stringlabel = "Old" || stringlabel = "Pre" then
	let is_ptr =
	  match term.term_node with TLval(TMem _,_) -> true | _ -> false in
	if is_ptr then in_old_ptr <- true;
	in_old_term <- true;
	let v = self#term term in
	if is_ptr then in_old_ptr <- false;
	in_old_term <- false;
	v
      else
	(* label Post is only encoutered in post-conditions, and \at(t,Post)
	   in a post-condition is t *)
	if stringlabel = "Post" || stringlabel = "Here" then
	  self#term term
	else
	  begin
	    if current_function <> None then
	      Sd_options.Self.warning "%a unsupported" Printer.pp_term t;
	    assert false (* TODO ? *)
	  end

    | Tbase_addr _ -> Sd_options.Self.not_yet_implemented "Tbase_addr"
    | Toffset _ -> Sd_options.Self.not_yet_implemented "Toffset"
    | Tblock_length _ -> Sd_options.Self.not_yet_implemented "Tblock_length"
    | Tnull -> [], Ctype_fragment Zero

    (* C type -> logic type *)
    | TLogic_coerce (_, t')
    | TCoerceE (t', {term_type=(Linteger|Lreal)}) ->
      begin
	match ty with
	| Linteger ->
	  let ty' =
	    match t'.term_type with
	    | Ctype x -> Ctype (Cil.unrollType x)
	    | x -> x
	  in
	  let inserts_0, v = self#term t' in
	  let v = self#ctype_fragment v in
	  let fresh_var = self#fresh_gmp_var() in
	  let insert_1, decl_var = self#decl_gmp_var fresh_var in
	  let init_set =
	    match ty' with
	    | Ctype x when Cil.isUnsignedInteger x -> self#init_set_ui_gmp_var
	    | Ctype x when Cil.isSignedInteger x -> self#init_set_si_gmp_var
	    | _ -> assert false
	  in
	  let insert_2, init_var = init_set decl_var v in
	  inserts_0 @ [insert_1; insert_2], Gmp_fragment init_var
	| Lreal -> assert false (* TODO: reals *)
	| _ -> assert false (* unreachable *)
      end

    (* logic type -> C type *)
    | TCoerce (t', ty')
    | TCoerceE (t', {term_type=Ctype ty'}) ->
      begin
	match t'.term_type with
	| Linteger ->
	  let inserts_0, v = self#term t' in
	  let v = self#gmp_fragment v in
	  let var = self#fresh_ctype_var ty' in
	  let insert_1 = Decl_ctype_var var in
	  let value =
	    match ty' with
	    | x when Cil.isUnsignedInteger x -> Gmp_get_ui v
	    | x when Cil.isSignedInteger x -> Gmp_get_si v
	    | _ -> assert false
	  in
	  let insert_2 = Instru(Affect(var,value)) in
	  let insert_3 = Instru(Gmp_clear v) in
	  inserts_0 @ [insert_1; insert_2; insert_3], Ctype_fragment var
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
  (* end term *)

  method private tlval (tlhost, toffset) =
    match tlhost with
    | TResult _ ->
      let var = Extlib.the result_varinfo in
      [], Ctype_fragment (My_ctype_var(var.vtype, var.vname))
    | _ ->
      let inserts_0, lhost = self#tlhost tlhost in
      let rec aux insertions ret = function
	| TNoOffset -> insertions, ret
	| TField (fi, tof) -> aux insertions (Field(ret, fi.fname)) tof
	| TModel _ -> assert false (* TODO *)
	| TIndex (t, tof) ->
	  let inserts_1, t' = self#term t in
	  begin
	    match t.term_type with
	    | Linteger ->
	      aux (insertions @ inserts_1)
		(Index(ret, Gmp_get_si(self#gmp_fragment t'))) tof
	    | Lreal -> assert false (* unreachable *)
	    | _ -> aux insertions (Index(ret, self#ctype_fragment t')) tof
	  end
      in
      match lhost with
      | Gmp_fragment _ -> (* TODO *)
	assert (toffset = TNoOffset);
	inserts_0, lhost
      | Ctype_fragment lhost' ->
	let insertions, ret = aux inserts_0 lhost' toffset in
	insertions, Ctype_fragment ret

  method private tlhost lhost =
    match lhost with
    | TVar lv -> [], self#logic_var lv
    | TResult _ -> assert false
    | TMem t ->
      let inserts_0, t' = self#term t in
      inserts_0, Ctype_fragment (Deref (self#ctype_fragment t'))

  (* modify result_varinfo when the function returns something *)
  method private compute_result_varinfo fct =
    let rec do_stmts = function
      | [] -> ()
      | {skind=Return(Some{enode=Lval(Var v,_)},_)}::_ -> result_varinfo<-Some v
      | _ :: t -> do_stmts t
    in
    do_stmts fct.sallstmts

  method private at_least_one_prop kf behaviors =
    let in_ensures b r k =
      r || (List.mem (Property.ip_of_ensures kf Kglobal b k) props) in
    let in_bhv r b = r || List.fold_left (in_ensures b) false b.b_post_cond in
    List.fold_left in_bhv false behaviors

  method! vfunc f =
    let entry_point = Kernel_function.get_name (fst(Globals.entry_point())) in
    let kf = Globals.Functions.find_by_name f.svar.vname in
    let behaviors = Annotations.behaviors kf in
    self#compute_result_varinfo f;

    (* BEGIN precond (entry-point) *)
    if f.svar.vname = entry_point then
      begin
	current_label <- Some (BegFunc (f.svar.vname ^ "_precond"));
	List.iter (fun b ->
	  let preconds =
	    List.rev_append (List.rev (Sd_utils.typically_preds b)) b.b_requires
	  in
	  let not_translated p =
	    Sd_states.Not_Translated_Predicates.fold_left
	      (fun b e -> b || e = p.ip_id) false
	  in
	  let preconds = List.filter not_translated preconds in
	  let do_precond p =
	    let inserts, v = self#predicate(self#subst_pred p.ip_content) in
	    if v <> True then (* untreated predicates are translated as True *)
	      inserts @ [If(Lnot v, [Instru(Ret Zero)], [])]
	    else
	      inserts
	  in
	  if preconds <> [] then
	    if b.b_assumes <> [] then
	      let inserts_0, exp = self#cond_of_assumes b.b_assumes in
	      let inserts_then =
		List.fold_left (@) [] (List.map do_precond preconds) in
	      let insert_1 = If(exp, inserts_then, []) in
	      let inserts = inserts_0 @ [insert_1] in
	      List.iter self#insert inserts
	    else
	      let inserts =
		List.fold_left (@) [] (List.map do_precond preconds) in
	      List.iter self#insert inserts
	) behaviors;
      end
    (* END precond (entry-point) *)
    (* BEGIN precond (not entry-point) *)
    else
      begin
	current_label <- Some (BegFunc f.svar.vname);
	List.iter (fun b ->
	  let pre = b.b_requires in
	  let to_prop = Property.ip_of_requires kf Kglobal b in
	  let pre = List.filter (fun p -> List.mem (to_prop p) props) pre in
	  let do_precond pred =
	    let prop = to_prop pred in
	    let id = Sd_utils.to_id prop in
	    self#pc_assert_exception pred.ip_content "Pre-condition!" id prop
	  in
	  if pre <> [] then
	    if b.b_assumes <> [] then
	      let inserts_0, exp = self#cond_of_assumes b.b_assumes in
	      let inserts_t = List.fold_left (@) [] (List.map do_precond pre) in
	      let insert_1 = If(exp, inserts_t, []) in
	      let inserts = inserts_0 @ [insert_1] in
	      List.iter self#insert inserts
	    else
	      let inserts = List.fold_left (@) [] (List.map do_precond pre) in
	      List.iter self#insert inserts
	) behaviors
      end;
    (* END precond (not entry-point) *)

    current_label <- Some (EndFunc f.svar.vname);

    (* BEGIN postcond *)
    if (self#at_least_one_prop kf behaviors)
      || (Sd_options.Behavior_Reachability.get()) then
      begin
	let do_behavior b =
	  let post = b.b_post_cond in
	  let to_prop = Property.ip_of_ensures kf Kglobal b in
	  let post = List.filter (fun x -> List.mem (to_prop x) props) post in
	  let do_postcond (tk,pred) =
	    let prop = to_prop (tk,pred) in
	    let id = Sd_utils.to_id prop in
	    self#pc_assert_exception pred.ip_content "Post-condition!" id prop
	  in
	  let str = Format.sprintf "@@FC:REACHABLE_BHV:%i" bhv_to_reach_cpt in
	  let add_reach_info =
	    not (Cil.is_default_behavior b)
	    && (Sd_options.Behavior_Reachability.get())
	  in
	  if post <> [] || (Sd_options.Behavior_Reachability.get()) then
	    begin
	      if b.b_assumes <> [] then
		let inserts_0, exp = self#cond_of_assumes b.b_assumes in
		let inserts_then_0 =
		  if add_reach_info then
		    begin
		      Sd_states.Behavior_Reachability.replace bhv_to_reach_cpt
			(kf, b, false);
		      bhv_to_reach_cpt <- bhv_to_reach_cpt+1;
		      [Instru(Pc_to_framac str)]
		    end
		  else
		    []
		in
		let inserts_then_1 =
		  List.fold_left (@) [] (List.map do_postcond post) in
		let insert_1 = If(exp, inserts_then_0 @ inserts_then_1, []) in
		inserts_0 @ [insert_1]
	      else
		let inserts_0 = 
		  if add_reach_info then
		    begin
		      Sd_states.Behavior_Reachability.replace bhv_to_reach_cpt
			(kf, b, false);
		      bhv_to_reach_cpt <- bhv_to_reach_cpt+1;
		      [Instru(Pc_to_framac str)]
		    end
		  else
		    []
		in
		let inserts_1 =
		  List.fold_left (@) [] (List.map do_postcond post) in
		inserts_0 @ inserts_1
	    end
	  else
	    []
	in
	let inserts = List.fold_left (@) [] (List.map do_behavior behaviors) in
	self#insert (Block inserts)
      end;
    (* END postcond *)

    current_label <- Some (BegFunc f.svar.vname);

    (* alloc variables for \at terms *)
    let dig_type = function
      | TPtr(ty,_) | TArray(ty,_,_,_) -> ty
      | ty -> Sd_options.Self.abort "dig_type %a" Printer.pp_typ ty
    in
    let dig_type x = dig_type (Cil.unrollTypeDeep x) in
    let lengths = Sd_utils.lengths_from_requires kf in
    let do_varinfo v =
      let terms =
	try Cil_datatype.Varinfo.Hashtbl.find lengths v
	with Not_found -> []
      in
      let my_v = My_ctype_var(v.vtype, v.vname) in
      let my_old_v = My_ctype_var(v.vtype, "old_"^v.vname) in
      self#insert (Decl_ctype_var my_old_v);
      self#insert (Instru(Affect(my_old_v, my_v)));
      let rec alloc_aux my_old_ptr my_ptr ty = function
	| h :: t ->
	  let ty = dig_type ty in
	  let inserts_0, h' = self#term h in
	  let my_iterator = self#fresh_ctype_var Cil.intType in
	  let insert_1 = Decl_ctype_var my_iterator in
	  begin
	    match h.term_type with
	    | Linteger ->
	      let h' = self#gmp_fragment h' in
	      let malloc = Malloc(Binop(Mult,(Gmp_get_si h'), Sizeof ty)) in
	      let insert_2 = Instru(Affect(my_old_ptr, malloc)) in
	      let my_new_old_ptr = Index(my_old_ptr, my_iterator) in
	      let my_new_ptr = Index(my_ptr, my_iterator) in
	      let inserts_block = alloc_aux my_new_old_ptr my_new_ptr ty t in
	      let init = Affect(my_iterator, Zero) in
	      let cond = Cmp(Rlt, my_iterator, Gmp_get_si h') in
	      let step = Affect(my_iterator, (Binop(PlusA, my_iterator,One))) in
	      let insert_3 = For(Some init,Some cond,Some step,inserts_block) in
	      let insert_4 = Instru(Gmp_clear h') in
	      inserts_0 @ [insert_1; insert_2; insert_3; insert_4]
	    | Lreal -> assert false (* TODO: reals *)
	    | _ ->
	      let h' = self#ctype_fragment h' in
	      let insert_2 =
		Instru(Affect(my_old_ptr, Malloc(Binop(Mult,h', Sizeof ty)))) in
	      let my_new_old_ptr = Index(my_old_ptr, my_iterator) in
	      let my_new_ptr = Index(my_ptr, my_iterator) in
	      let inserts_block = alloc_aux my_new_old_ptr my_new_ptr ty t in
	      let init = Affect(my_iterator, Zero) in
	      let cond = Cmp(Rlt, my_iterator, h') in
	      let step = Affect(my_iterator, (Binop(PlusA, my_iterator,One))) in
	      let insert_3 = For(Some init,Some cond,Some step,inserts_block) in
	      inserts_0 @ [insert_1; insert_2; insert_3]
	  end
	| [] -> [Instru(Affect(my_old_ptr, my_ptr))]
      in
      if Cil.isPointerType v.vtype || Cil.isArrayType v.vtype then
	begin
	  let my_old_ptr = My_ctype_var(v.vtype, "old_ptr_"^v.vname) in
	  self#insert (Decl_ctype_var my_old_ptr);
	  let inserts = alloc_aux my_old_ptr my_v v.vtype terms in
	  List.iter self#insert inserts;
	end
    in
    List.iter do_varinfo visited_globals;
    List.iter do_varinfo (Kernel_function.get_formals kf);

    current_label <- Some (EndFunc f.svar.vname);

    (* dealloc variables for \at terms *)
    begin
      let lengths = Sd_utils.lengths_from_requires kf in
      let do_varinfo v =
	let terms =
	  try Cil_datatype.Varinfo.Hashtbl.find lengths v
	  with Not_found -> []
	in
	let rec dealloc_aux my_old_ptr = function
	  | [] -> []
	  | _ :: [] -> [Instru(Free my_old_ptr)]
	  | h :: t ->
	    let my_iterator = self#fresh_ctype_var Cil.intType in
	    let insert_0 = Decl_ctype_var my_iterator in
	    let inserts_1, h' = self#term h in
	    let inserts' =
	      match h.term_type with
	      | Linteger ->
		let h' = self#gmp_fragment h' in
		let inserts_block=dealloc_aux(Index(my_old_ptr,my_iterator))t in
		let init = Affect(my_iterator, Zero) in
		let cond = Cmp(Rlt, my_iterator, Gmp_get_si h') in
		let step = Affect(my_iterator,(Binop(PlusA,my_iterator,One))) in
		let insert_2=For(Some init,Some cond,Some step,inserts_block) in
		let insert_3 = Instru(Gmp_clear h') in
		[insert_2; insert_3]
	      | Lreal -> assert false (* TODO: reals *)
	      | _ ->
		let h' = self#ctype_fragment h' in
		let inserts_block=dealloc_aux(Index(my_old_ptr,my_iterator))t in
		let init = Affect(my_iterator, Zero) in
		let cond = Cmp(Rlt, my_iterator, h') in
		let step = Affect(my_iterator,(Binop(PlusA,my_iterator,One))) in
		let insert_2=For(Some init,Some cond,Some step,inserts_block) in
		[insert_2]
	    in
	    [insert_0] @ inserts_1 @ inserts' @ [Instru(Free(my_old_ptr))]
	in
	let my_old_ptr = My_ctype_var(Cil.voidPtrType, "old_ptr_"^v.vname) in
	let insertions = dealloc_aux my_old_ptr terms in
	List.iter self#insert insertions
      in
      List.iter do_varinfo visited_globals;
      List.iter do_varinfo (Kernel_function.get_formals kf)
    end;

    current_label <- None;

    Cil.DoChildren
  (* end vfunc *)

  method private subst_pred p = (new Sd_subst.subst)#subst_pred p [] [] [] []

  method private cond_of_assumes pred_list =
    let rec aux insertions ret = function
      | [] -> insertions, ret
      | h :: t ->
	let ins, v = self#predicate (self#subst_pred h.ip_content) in
	aux (insertions @ ins) (Land(ret, v)) t
    in
    aux [] True pred_list

  method private cond_of_behaviors pred_lists =
    let rec aux insertions ret = function
      | [] -> insertions, ret
      | h :: t ->
	let ins, v = self#cond_of_assumes h in
	aux (insertions @ ins) (Lor(ret, v)) t
      in
    aux [] False pred_lists

  method private pc_assert_exception pred msg id prop =
    let inserts_0, var = self#predicate (self#subst_pred pred) in
    let insert_1 = If(Lnot var, [Instru(Pc_exn(msg, id))], []) in
    translated_properties <- prop :: translated_properties;
    inserts_0 @ [insert_1]

  method! vcode_annot ca =
    let stmt = Extlib.the self#current_stmt in
    let kf = Kernel_function.find_englobing_kf stmt in
    let bhv_names =
      match ca.annot_content with
      | AAssert (b,_) | AStmtSpec (b,_) | AInvariant (b,_,_) -> b
      | _ -> []
    in
    let on_behavior s _ b ret = if b.b_name = s then b.b_assumes else ret in
    let on_behavior_name s = Annotations.fold_behaviors (on_behavior s) kf [] in
    let behaviors = List.map on_behavior_name bhv_names in
    begin
      match ca.annot_content with
      | AStmtSpec (_,bhvs) ->
	
	current_label <- Some (BegStmt stmt.sid);

	let do_behavior b =
	  let pre = b.b_requires in
	  let to_prop = Property.ip_of_requires kf (Kstmt stmt) b in
	  let pre = List.filter (fun p -> List.mem (to_prop p) props) pre in
	  let do_precond pred =
	    let prop = to_prop pred in
	    let id = Sd_utils.to_id prop in
	    self#pc_assert_exception
	      pred.ip_content "Stmt Pre-condition!" id prop
	  in
	  if pre <> [] then
	    if b.b_assumes <> [] then
	      let inserts_0, exp = self#cond_of_assumes b.b_assumes in
	      let inserts_then =
		List.fold_left (@) [] (List.map do_precond pre) in
	      let insert_1 = If(exp, inserts_then, []) in
	      inserts_0 @ [insert_1]
	    else
	      List.fold_left (@) [] (List.map do_precond pre)
	  else
	    []
	in
	if behaviors <> [] then
	  let inserts_0, cond = self#cond_of_behaviors behaviors in
	  let inserts_then =
	    List.fold_left (@) [] (List.map do_behavior bhvs.spec_behavior) in
	  let insert_1 = If(cond, inserts_then, []) in
	  let inserts = inserts_0 @ [insert_1] in
	  List.iter self#insert inserts
	else
	  begin
	    let inserts =
	      List.fold_left (@) [] (List.map do_behavior bhvs.spec_behavior) in
	    List.iter self#insert inserts
	  end;
	  
	current_label <- Some (EndStmt stmt.sid);
	
	if self#at_least_one_prop kf bhvs.spec_behavior then
	  begin
	    let do_behavior b =
	      let post = b.b_post_cond in
	      let to_prop = Property.ip_of_ensures kf (Kstmt stmt) b in
	      let post =
		List.filter (fun x -> List.mem (to_prop x) props) post in
	      let do_postcond ((_,pred) as k) =
		let prop = to_prop k in
		let id = Sd_utils.to_id prop in
		self#pc_assert_exception pred.ip_content
		  "Stmt Post-condition!" id prop
	      in
	      if post <> [] then
		if b.b_assumes <> [] then
		  let inserts_0, exp = self#cond_of_assumes b.b_assumes in
		  let inserts_then =
		    List.fold_left (@) [] (List.map do_postcond post) in
		  let insert_1 = If(exp, inserts_then, []) in
		  inserts_0 @ [insert_1]
		else
		  List.fold_left (@) [] (List.map do_postcond post)
	      else
		[]
	    in
	    if behaviors <> [] then
	      let inserts_0, cond = self#cond_of_behaviors behaviors in
	      let inserts_then =
		List.fold_left (@) [] (List.map do_behavior bhvs.spec_behavior)
	      in
	      let insert_1 = If(cond, inserts_then, []) in
	      let inserts = inserts_0 @ [insert_1] in
	      List.iter self#insert inserts
	    else
	      let inserts =
		List.fold_left (@) [] (List.map do_behavior bhvs.spec_behavior)
	      in
	      List.iter self#insert inserts
	  end;

	current_label <- None

      | AAssert (_,pred) ->

	current_label <- Some (BegStmt stmt.sid);

	let prop = Property.ip_of_code_annot_single kf stmt ca in
	if List.mem prop props then
	  begin
	    let id = Sd_utils.to_id prop in
	    if behaviors <> [] then
	      let inserts_0, cond = self#cond_of_behaviors behaviors in
	      let inserts_then =
		self#pc_assert_exception pred.content "Assert!" id prop in
	      let insert_1 = If(cond, inserts_then, []) in
	      let inserts = inserts_0 @ [insert_1] in
	      List.iter self#insert inserts
	    else
	      let ins =
		self#pc_assert_exception pred.content "Assert!" id prop in
	      List.iter self#insert ins
	  end;

	current_label <- None

      | AInvariant (_,true,pred) ->

	let prop = Property.ip_of_code_annot_single kf stmt ca in
	if List.mem prop props then
	  let id = Sd_utils.to_id prop in
	  let f msg =
	    if behaviors <> [] then
	      let inserts_0, cond = self#cond_of_behaviors behaviors in
	      let inserts_then =
		self#pc_assert_exception pred.content msg id prop in
	      let insert_1 = If(cond, inserts_then, []) in
	      let inserts = inserts_0 @ [insert_1] in
	      List.iter self#insert inserts
	    else
	      let ins = self#pc_assert_exception pred.content msg id prop in
	      List.iter self#insert ins
	  in
	  current_label <- Some (BegStmt stmt.sid);
	  f "Loop invariant not established!";
	  current_label <- Some (EndIter stmt.sid);
	  f "Loop invariant not preserved!";
	  current_label <- None

      | AVariant (term,_) ->

	let prop = Property.ip_of_code_annot_single kf stmt ca in
	if List.mem prop props then
	  let id = Sd_utils.to_id prop in
	  begin
	    match term.term_type with
	    | Linteger ->
	      current_label <- Some (BegStmt stmt.sid);
	      let inserts_0, term' = self#term term in
	      List.iter self#insert inserts_0;
	      let term' = self#gmp_fragment term' in
	      let cond = Gmp_cmp_ui(Lt, term', Zero) in
	      let instr = Instru(Pc_exn("Variant non positive", id)) in
	      self#insert (If (cond, [instr], []));
	      current_label <- Some (EndStmt stmt.sid);
	      self#insert (Instru(Gmp_clear term'));
	      current_label <- Some (BegIter stmt.sid);
	      let inserts_1, term' = self#term term in
	      List.iter self#insert inserts_1;
	      let term' = self#gmp_fragment term' in
	      let fresh_variant = self#fresh_gmp_var() in
	      let insert_2, decl_variant = self#decl_gmp_var fresh_variant in
	      self#insert insert_2;
	      let insert_3, init_variant =
		self#init_set_gmp_var decl_variant term' in
	      self#insert insert_3;
	      current_label <- Some (EndIter stmt.sid);
	      let inserts_4, term' = self#term term in
	      List.iter self#insert inserts_4;
	      let term' = self#gmp_fragment term' in
	      let cond = Gmp_cmp_ui(Lt, init_variant, Zero) in
	      let instr = Instru(Pc_exn("Variant non positive", id)) in
	      self#insert (If(cond, [instr], []));
	      let cond = Gmp_cmp(Ge, term', init_variant) in
	      let instr = Instru(Pc_exn("Variant non decreasing", id)) in
	      self#insert (If(cond, [instr] ,[]));
	      self#insert (Instru(Gmp_clear init_variant));
	      current_label <- None
	    | Lreal -> assert false (* TODO: reals *)
	    | _ ->
	      current_label <- Some (BegStmt stmt.sid);
	      let inserts_0, term' = self#term term in
	      List.iter self#insert inserts_0;
	      let term' = self#ctype_fragment term' in
	      let cond = Cmp(Rlt, term', Zero) in
	      let instr = Instru(Pc_exn("Variant non positive", id)) in
	      self#insert (If(cond, [instr], []));
	      current_label <- Some (EndStmt stmt.sid);
	      current_label <- Some (BegIter stmt.sid);
	      let inserts_1, term' = self#term term in
	      List.iter self#insert inserts_1;
	      let term' = self#ctype_fragment term' in
	      let variant = self#fresh_ctype_var Cil.intType in
	      self#insert (Decl_ctype_var variant);
	      self#insert (Instru(Affect(variant, term')));
	      current_label <- Some (EndIter stmt.sid);
	      let inserts_2, term' = self#term term in
	      List.iter self#insert inserts_2;
	      let term' = self#ctype_fragment term' in
	      let cond = Cmp(Rlt, variant, Zero) in
	      let instr = Instru(Pc_exn("Variant non positive", id)) in
	      self#insert (If(cond, [instr], []));
	      let cond = Cmp(Rge, term', variant) in
	      let instr = Instru(Pc_exn("Variant non decreasing", id)) in
	      self#insert (If(cond, [instr], []));
	      current_label <- None
	  end;
	  translated_properties <- prop :: translated_properties
      | _ -> ()
    end;
    Cil.DoChildren
  (* end vcode_annot *)

  method! vstmt_aux stmt =
    if List.mem stmt.sid stmts_to_reach then
      begin
	current_label <- Some (BegStmt stmt.sid);
	let str = Format.sprintf "@@FC:REACHABLE_STMT:%i" stmt.sid in
	self#insert (Instru(Pc_to_framac str));
	current_label <- None
      end;
    let kf = Kernel_function.find_englobing_kf stmt in
    begin
      match stmt.skind with
      | Cil_types.If(_exp,b1,b2,_loc) ->
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
	end
      | _ -> ()
    end;
    Cil.DoChildren

  method! vglob_aux g =
    begin
      match g with
      | GFun (fundec, _l) ->
	self#in_current_function fundec.svar;
	let after globs = self#out_current_function; globs in
	Cil.ChangeDoChildrenPost ([g], after)
      | GVar(vi,_,_) -> visited_globals <- vi::visited_globals; Cil.DoChildren
      | _ -> Cil.DoChildren
    end

  method private predicate_named pnamed : insertion list * pred_expr =
    self#predicate pnamed.content

  method private quantif_predicate ~forall logic_vars hyps goal =
    if (List.length logic_vars) > 1 then
      failwith "quantification on many variables unsupported!";
    let var = self#fresh_pred_var() in
    let guards, vars = Sd_utils.compute_guards [] logic_vars hyps in
    if vars <> [] then
      failwith "Unguarded variables in quantification!";
    let t1,r1,lv,r2,t2 = List.hd guards in
    let iter_name = lv.lv_name in
    let insert_0 = Decl_pred_var var in
    let insert_1 = Instru(Affect_pred(var, (if forall then True else False))) in
    let inserts_3 =
      match t1.term_type with
      | Linteger ->
	begin
	  match t2.term_type with
	  | Linteger ->
	    let fresh_iter = My_gmp_var iter_name in
	    let insert_0, decl_iter = self#decl_gmp_var fresh_iter in
	    let inserts_1, t1' = self#term t1 in
	    let t1' = self#gmp_fragment t1' in
	    let inserts_2, t2' = self#term t2 in
	    let t2' = self#gmp_fragment t2' in
	    let insert_3, init_iter = self#init_set_gmp_var decl_iter t1' in
	    let inserts_4 =
	      if r1 = Rlt then
		[Instru(Gmp_binop_ui(PlusA,init_iter,init_iter,One))]
	      else []
	    in
	    let exp1 = Gmp_cmpr(r2, init_iter, t2') in
	    let exp2 = if forall then var else Lnot var in
	    let inserts_block =
	      let ins_b_0, goal_var = self#predicate_named goal in
	      let ins_b_1 = Instru(Affect_pred(var, goal_var)) in
	      let ins_b_2 =
		Instru(Gmp_binop_ui(PlusA, init_iter, init_iter,One)) in
	      ins_b_0 @ [ins_b_1; ins_b_2]
	    in
	    let insert_5 =
	      For(None, Some(Land(exp1, exp2)), None, inserts_block) in
	    let insert_6 = Instru(Gmp_clear init_iter) in
	    let insert_7 = Instru(Gmp_clear t1') in
	    let insert_8 = Instru(Gmp_clear t2') in
	    [insert_0] @ inserts_1 @ inserts_2 @ [insert_3] @ inserts_4
	    @ [insert_5; insert_6; insert_7; insert_8]
	  | Lreal -> assert false (* TODO: reals *)
	  | _ ->
	    let fresh_iter = My_gmp_var iter_name in
	    let insert_0, decl_iter = self#decl_gmp_var fresh_iter in
	    let inserts_1, t1' = self#term t1 in
	    let t1' = self#gmp_fragment t1' in
	    let inserts_2, t2' = self#term t2 in
	    let t2' = self#ctype_fragment t2' in
	    let insert_3, init_iter = self#init_set_gmp_var decl_iter t1' in
	    let inserts_4 =
	      if r1 = Rlt then
		[Instru(Gmp_binop_ui(PlusA,init_iter,init_iter,One))]
	      else []
	    in
	    let exp1 = Gmp_cmpr_si(r2, init_iter, t2') in
	    let exp2 = if forall then var else Lnot var in
	    let inserts_block =
	      let ins_b_0, goal_var = self#predicate_named goal in 
	      let ins_b_1 = Instru(Affect_pred(var, goal_var)) in
	      let ins_b_2 =
		Instru(Gmp_binop_ui(PlusA, init_iter, init_iter,One)) in
	      ins_b_0 @ [ins_b_1; ins_b_2]
	    in
	    let insert_5 = For(None,Some(Land(exp1,exp2)),None,inserts_block) in
	    let insert_6 = Instru(Gmp_clear init_iter) in
	    let insert_7 = Instru(Gmp_clear t1') in
	    [insert_0] @ inserts_1 @ inserts_2 @ [insert_3] @ inserts_4
	    @ [insert_5; insert_6; insert_7]
	end
      | Lreal -> assert false (* TODO: reals *)
      | _ ->
	let iter = My_ctype_var (Cil.intType, iter_name) in
	let insert_0 = Decl_ctype_var iter in
	let inserts_1, t1' = self#term t1 in
	let t1' = self#ctype_fragment t1' in
	let inserts_2, t2' = self#term t2 in
	let t2' = self#ctype_fragment t2' in
	let exp1 = Affect(iter, (match r1 with
	  | Rlt -> Binop(PlusA,t1',One)
	  | Rle -> t1'
	  | _ -> assert false))
	in
	let exp2 =Land((Cmp(r2,iter,t2')),(if forall then var else Lnot var)) in
	let exp3 = Affect(iter,Binop(PlusA,iter,One)) in
	let inserts_block =
	  let ins_b_0, goal_var = self#predicate_named goal in
	  let ins_b_1 = Instru(Affect_pred(var, goal_var)) in
	  ins_b_0 @ [ins_b_1]
	in
	let insert_3 = For(Some exp1, Some exp2, Some exp3, inserts_block) in
	[insert_0] @ inserts_1 @ inserts_2 @ [insert_3]
    in
    let insert_4 = Block inserts_3 in
    [insert_0; insert_1; insert_4], var
  (* end of quantif_predicate *)

  method private predicate pred : insertion list * pred_expr =
    match pred with
    | Ptrue -> [], True
    | Pfalse -> [], False
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
      begin
	match offset.term_type with
	| Linteger ->
	  let inserts_0, x' = self#term pointer in
	  let x' = self#ctype_fragment x' in
	  let inserts_1, y' = self#term offset in
	  let y' = self#gmp_fragment y' in
	  let var = self#fresh_pred_var() in
	  let insert_2 = Decl_pred_var var in
	  let exp1 = Gmp_cmp_ui(Ge, y', Zero) in
	  let exp2 = Gmp_cmp_ui(Lt, y', Pc_dim(x')) in
	  let insert_3 = Instru(Affect_pred(var, Land(exp1, exp2))) in
	  let insert_4 = Instru(Gmp_clear y') in
	  inserts_0 @ inserts_1 @ [insert_2; insert_3; insert_4], var
	| Lreal -> assert false (* unreachable *)
	| Ctype (TInt _) ->
	  let inserts_0, x' = self#term pointer in
	  let x' = self#ctype_fragment x' in
	  let inserts_1, y' = self#term offset in
	  let y' = self#ctype_fragment y' in
	  let exp1 = Cmp(Rge, y', Zero) in
	  let exp2 = Cmp(Rgt, Pc_dim(x'), y') in
	  inserts_0 @ inserts_1, Land(exp1, exp2)
	| _ -> assert false (* unreachable *)
      end
    | Pforall(logic_vars,{content=Pimplies(hyps,goal)}) ->
      self#quantif_predicate ~forall:true logic_vars hyps goal
    | Pexists(logic_vars,{content=Pand(hyps,goal)}) ->
      self#quantif_predicate ~forall:false logic_vars hyps goal
    | Pforall _ -> failwith "\\forall not of the form \\forall ...; a ==> b;"
    | Pexists _ -> failwith "\\exists not of the form \\exists ...; a && b;"
    | Pnot(pred1) ->
      let ins, pred1_var = self#predicate_named pred1 in
      ins, Lnot pred1_var
    | Pand(pred1,pred2) ->
      let var = self#fresh_pred_var() in
      let inserts_0, pred1_var = self#predicate_named pred1 in
      let insert_1 = Decl_pred_var var in
      let insert_2 = Instru(Affect_pred(var, pred1_var)) in
      let inserts_b_0, pred2_var = self#predicate_named pred2 in
      let insert_b_1 = Instru(Affect_pred(var, pred2_var)) in
      let insert_3 = If(var, inserts_b_0 @ [insert_b_1], []) in
      inserts_0 @ [insert_1; insert_2; insert_3], var
    | Por(pred1,pred2) ->
      let var = self#fresh_pred_var()  in
      let inserts_0, pred1_var = self#predicate_named pred1 in
      let insert_1 = Decl_pred_var var in
      let insert_2 = Instru(Affect_pred(var, pred1_var)) in
      let inserts_b_0, pred2_var = self#predicate_named pred2 in
      let insert_b_1 = Instru(Affect_pred(var, pred2_var)) in
      let insert_3 = If(var, [], inserts_b_0 @ [insert_b_1]) in
      inserts_0 @ [insert_1; insert_2; insert_3], var
    | Pimplies(pred1,pred2) ->
      let var = self#fresh_pred_var() in
      let insert_0 = Decl_pred_var var in
      let insert_1 = Instru(Affect_pred(var, True)) in
      let inserts_2, pred1_var = self#predicate_named pred1 in
      let inserts_b_0, pred2_var = self#predicate_named pred2 in
      let insert_b_1 = Instru(Affect_pred(var, pred2_var)) in
      let insert_3 = If(pred1_var, inserts_b_0 @ [insert_b_1], []) in
      [insert_0; insert_1] @ inserts_2 @ [insert_3], var
    | Piff(pred1,pred2) ->
      let inserts_0, pred1_var = self#predicate_named pred1 in
      let inserts_1, pred2_var = self#predicate_named pred2 in
      let exp1 = Lor(Lnot pred1_var, pred2_var) in
      let exp2 = Lor(Lnot pred2_var, pred1_var) in
      inserts_0 @ inserts_1, Land(exp1, exp2)
    | Pif (t,pred1,pred2) -> (* untested *)
      begin
	let inserts_0, term_var = self#term t in
	let res_var = self#fresh_pred_var() in
	let insert_1 = Decl_pred_var res_var in
	let f () =
	  let term_var = self#ctype_fragment term_var in
	  let cond = Cmp(Rneq,term_var,Zero) in
	  let inserts_then_0, pred1_var = self#predicate_named pred1 in
	  let insert_then_1 = Instru(Affect_pred(res_var, pred1_var)) in
	  let inserts_then = inserts_then_0 @ [insert_then_1] in
	  let inserts_else_0, pred2_var = self#predicate_named pred2 in
	  let insert_else_1 = Instru(Affect_pred(res_var, pred2_var)) in
	  let inserts_else = inserts_else_0 @ [insert_else_1] in
	  let insert_2 = If(cond, inserts_then, inserts_else) in
	  inserts_0 @ [insert_1; insert_2], res_var
	in
	match t.term_type with
	| Linteger ->
	  let term_var = self#gmp_fragment term_var in
	  let cond = Gmp_cmp_si(Ne, term_var, Zero) in
	  let inserts_then_0, pred1_var = self#predicate_named pred1 in
	  let insert_then_1 = Instru(Affect_pred(res_var, pred1_var)) in
	  let inserts_then = inserts_then_0 @ [insert_then_1] in
	  let inserts_else_0, pred2_var = self#predicate_named pred2 in
	  let insert_else_1 = Instru(Affect_pred(res_var, pred2_var)) in
	  let inserts_else = inserts_else_0 @ [insert_else_1] in
	  let insert_2 = If(cond, inserts_then, inserts_else) in
	  let insert_3 = Instru(Gmp_clear term_var) in
	  inserts_0 @ [insert_1; insert_2; insert_3], res_var
	| Lreal -> assert false (* unreachable *)
	| Ctype (TInt _) -> f ()
	| Ltype (lt,_) when lt.lt_name = Utf8_logic.boolean -> f ()
	| _ -> assert false (* unreachable *)
      end

    | Prel(rel,t1,t2) ->
      begin
	match t1.term_type, t2.term_type with
	| Linteger, Linteger ->
	  let var = self#fresh_pred_var() in
	  let inserts_0, t1' = self#term t1 in
	  let t1' = self#gmp_fragment t1' in
	  let inserts_1, t2' = self#term t2 in
	  let t2' = self#gmp_fragment t2' in
	  let insert_2 = Decl_pred_var var in
	  let insert_3 = Instru(Affect_pred(var, Gmp_cmpr(rel, t1', t2'))) in
	  let insert_4 = Instru(Gmp_clear t1') in
	  let insert_5 = Instru(Gmp_clear t2') in
	  inserts_0 @ inserts_1 @ [insert_2; insert_3; insert_4; insert_5], var
	| Linteger, Ctype x ->
	  let var = self#fresh_pred_var() in
	  let inserts_0, t1' = self#term t1 in
	  let t1' = self#gmp_fragment t1' in
	  let inserts_1, t2' = self#term t2 in
	  let t2' = self#ctype_fragment t2' in
	  let insert_2 = Decl_pred_var var in
	  let value =
	    if Cil.isUnsignedInteger x then Gmp_cmpr_ui(rel, t1', t2')
	    else if Cil.isSignedInteger x then Gmp_cmpr_si(rel, t1', t2')
	    else assert false
	  in
	  let insert_3 = Instru(Affect_pred(var, value)) in
	  let insert_4 = Instru(Gmp_clear t1') in
	  inserts_0 @ inserts_1 @ [insert_2; insert_3; insert_4], var
	| Lreal, Lreal -> assert false (* TODO: reals *)
	| Ctype x, Linteger ->
	  let var = self#fresh_pred_var() in
	  let inserts_0, t1' = self#term t1 in
	  let t1' = self#ctype_fragment t1' in
	  let inserts_1, t2' = self#term t2 in
	  let t2' = self#gmp_fragment t2' in
	  let fresh_var' = self#fresh_gmp_var() in
	  let insert_2, decl_var' = self#decl_gmp_var fresh_var' in
	  let init_set =
	    if Cil.isUnsignedInteger x then self#init_set_ui_gmp_var
	    else if Cil.isSignedInteger x then self#init_set_si_gmp_var
	    else assert false
	  in
	  let insert_3, init_var' = init_set decl_var' t1' in
	  let insert_4 = Decl_pred_var var in
	  let insert_5 = Instru(Affect_pred(var,Gmp_cmpr(rel,init_var',t2'))) in
	  let insert_6 = Instru(Gmp_clear t2') in
	  let insert_7 = Instru(Gmp_clear init_var') in
	  inserts_0 @ inserts_1
	  @ [insert_2; insert_3; insert_4; insert_5; insert_6; insert_7], var
	| _ ->
	  let inserts_0, t1' = self#term t1 in
	  let t1' = self#ctype_fragment t1' in
	  let inserts_1, t2' = self#term t2 in
	  let t2' = self#ctype_fragment t2' in
	  inserts_0 @ inserts_1, Cmp(rel, t1', t2')
      end
      
    | Pat(p, LogicLabel(_,stringlabel)) when stringlabel = "Here" ->
      self#predicate_named p
    | Pat (p,_) ->
      Sd_options.Self.warning "%a unsupported!" Printer.pp_predicate pred;
      self#predicate_named p
    | _ ->
      Sd_options.Self.warning "%a unsupported" Printer.pp_predicate pred;
      [], True
(* end predicate *)
end



let pp_fresh_gmp fmt = function
  | Fresh_gmp_var id -> Format.fprintf fmt "__stady_gmp_%i" id
  | My_gmp_var name -> Format.fprintf fmt "%s" name

let pp_decl_gmp fmt = function
  | Declared_gmp_var v -> pp_fresh_gmp fmt v

let pp_init_gmp fmt = function
  | Initialized_gmp_var v -> pp_decl_gmp fmt v

let pp_gexpr fmt = pp_init_gmp fmt

let rec pp_cexpr fmt = function
  | Fresh_ctype_var (id, _ty) -> Format.fprintf fmt "__stady_term_%i" id
  | My_ctype_var (_, name) -> Format.fprintf fmt "%s" name
  | Zero -> Format.fprintf fmt "0"
  | One -> Format.fprintf fmt "1"
  | Cst s -> Format.fprintf fmt "%s" s
  | Gmp_get_ui g -> Format.fprintf fmt "__gmpz_get_ui(%a)" pp_gexpr g
  | Gmp_get_si g -> Format.fprintf fmt "__gmpz_get_si(%a)" pp_gexpr g
  | Unop (op, e) -> Format.fprintf fmt "%a(%a)" Printer.pp_unop op pp_cexpr e
  | Binop (op,x,y) ->
    Format.fprintf fmt "(%a %a %a)" pp_cexpr x Printer.pp_binop op pp_cexpr y
  | Pc_dim e -> Format.fprintf fmt "pathcrawler_dimension(%a)" pp_cexpr e
  | Malloc e -> Format.fprintf fmt "malloc(%a)" pp_cexpr e
  | Cast (t, e) -> Format.fprintf fmt "(%a)%a" Printer.pp_typ t pp_cexpr e
  | Sizeof t -> Format.fprintf fmt "sizeof(%a)" Printer.pp_typ t
  | Deref e -> Format.fprintf fmt "*%a" pp_cexpr e
  | Index (e, i) -> Format.fprintf fmt "%a[%a]" pp_cexpr e pp_cexpr i
  | Field (e, s) -> Format.fprintf fmt "%a.%s" pp_cexpr e s
  | Of_pred p -> Format.fprintf fmt "%a" pp_pexpr p

and pp_pexpr fmt = function
  | Fresh_pred_var id -> Format.fprintf fmt "__stady_pred_%i" id
  | True -> Format.fprintf fmt "1"
  | False -> Format.fprintf fmt "0"
  | Cmp (rel, e1, e2) ->
    Format.fprintf fmt "%a %a %a"pp_cexpr e1 Printer.pp_relation rel pp_cexpr e2
  | Gmp_cmp (op, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp(%a, %a) %a 0"
      pp_gexpr g1 pp_gexpr g2 Printer.pp_binop op
  | Gmp_cmp_ui (op, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp_ui(%a, %a) %a 0"
      pp_gexpr g1 pp_cexpr g2 Printer.pp_binop op
  | Gmp_cmp_si (op, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp_si(%a, %a) %a 0"
      pp_gexpr g1 pp_cexpr g2 Printer.pp_binop op
  | Gmp_cmpr (rel, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp(%a, %a) %a 0"
      pp_gexpr g1 pp_gexpr g2 Printer.pp_relation rel
  | Gmp_cmpr_ui (rel, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp_ui(%a, %a) %a 0"
      pp_gexpr g1 pp_cexpr g2 Printer.pp_relation rel
  | Gmp_cmpr_si (rel, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp_si(%a, %a) %a 0"
      pp_gexpr g1 pp_cexpr g2 Printer.pp_relation rel
  | Lnot p -> Format.fprintf fmt "!(%a)" pp_pexpr p
  | Land (p, p') -> Format.fprintf fmt "(%a && %a)" pp_pexpr p pp_pexpr p'
  | Lor (p, p') -> Format.fprintf fmt "(%a || %a)" pp_pexpr p pp_pexpr p'

let pp_garith fmt = function
  | PlusA -> Format.fprintf fmt "add"
  | MinusA -> Format.fprintf fmt "sub"
  | Mult -> Format.fprintf fmt "mul"
  | Div -> Format.fprintf fmt "tdiv_q"
  | Mod -> Format.fprintf fmt "tdiv_r"
  | _ -> assert false (* not used by the translation *)

let pp_instruction fmt = function
  | Affect (x,y) -> Format.fprintf fmt "%a = %a" pp_cexpr x pp_cexpr y
  | Affect_pred (x,y) -> Format.fprintf fmt "%a = %a" pp_pexpr x pp_pexpr y
  | Free e -> Format.fprintf fmt "free(%a)" pp_cexpr e
  | Pc_to_framac s -> Format.fprintf fmt "pathcrawler_to_framac(\"%s\")" s
  | Pc_exn(s,i)->Format.fprintf fmt"pathcrawler_assert_exception(\"%s\",%i)" s i
  | Ret e -> Format.fprintf fmt "return %a" pp_cexpr e
  | Gmp_clear g -> Format.fprintf fmt "__gmpz_clear(%a)" pp_gexpr g
  | Gmp_init g -> Format.fprintf fmt "__gmpz_init(%a)" pp_decl_gmp g
  | Gmp_init_set (g,g') ->
    Format.fprintf fmt "__gmpz_init_set(%a, %a)" pp_decl_gmp g pp_gexpr g'
  | Gmp_init_set_ui (g,c) ->
    Format.fprintf fmt "__gmpz_init_set_ui(%a, %a)" pp_decl_gmp g pp_cexpr c
  | Gmp_init_set_si (g,c) ->
    Format.fprintf fmt "__gmpz_init_set_si(%a, %a)" pp_decl_gmp g pp_cexpr c
  | Gmp_init_set_str (g,s) ->
    Format.fprintf fmt "__gmpz_init_set_str(%a, \"%s\", 10)" pp_decl_gmp g s
  | Gmp_set(g,h)-> Format.fprintf fmt "__gmpz_set(%a, %a)" pp_gexpr g pp_gexpr h
  | Gmp_abs(g,h)-> Format.fprintf fmt "__gmpz_abs(%a, %a)" pp_gexpr g pp_gexpr h
  | Gmp_ui_sub (r,a,b) ->
    Format.fprintf fmt "__gmpz_ui_sub(%a, %a, %a)"
      pp_gexpr r pp_cexpr a pp_gexpr b
  | Gmp_binop (op,r,a,b) ->
    Format.fprintf fmt "__gmpz_%a(%a, %a, %a)"
      pp_garith op pp_gexpr r pp_gexpr a pp_gexpr b
  | Gmp_binop_ui (op,r,a,b) ->
    Format.fprintf fmt "__gmpz_%a_ui(%a, %a, %a)"
      pp_garith op pp_gexpr r pp_gexpr a pp_cexpr b
  | Gmp_binop_si (op,r,a,b) ->
    Format.fprintf fmt "__gmpz_%a_si(%a, %a, %a)"
      pp_garith op pp_gexpr r pp_gexpr a pp_cexpr b

let rec pp_insertion ?(line_break = true) fmt ins =
  let rec aux fmt = function
    | [] -> ()
    | h :: [] -> pp_insertion ~line_break:false fmt h
    | h :: t -> pp_insertion ~line_break:true fmt h; aux fmt t
  in
  begin
    match ins with
    | Instru i -> Format.fprintf fmt "@[%a;@]" pp_instruction i
    | Decl_gmp_var v -> Format.fprintf fmt "@[mpz_t %a;@]" pp_fresh_gmp v
    | Decl_ctype_var ((Fresh_ctype_var (_id, ty)) as v) ->
      Format.fprintf fmt "@[%a %a;@]" Printer.pp_typ ty pp_cexpr v
    | Decl_ctype_var (My_ctype_var (ty, name)) ->
      Format.fprintf fmt "@[%a %s;@]" Printer.pp_typ ty name
    | Decl_ctype_var _ -> assert false
    | Decl_pred_var p -> Format.fprintf fmt "@[int %a;@]" pp_pexpr p
    | If (cond,b1,b2) ->
      Format.fprintf fmt "@[<hov 2>if(%a) {@\n%a@]@\n}" pp_pexpr cond aux b1;
      if b2 <> [] then
	Format.fprintf fmt "@\n@[<hov 2>else {@\n%a@]@\n}" aux b2
    | For(None, Some e, None, b) ->
      Format.fprintf fmt "@[<hov 2>while(%a) {@\n%a@]@\n}" pp_pexpr e aux b
    | For(Some i1, Some e, Some i2, b) ->
      Format.fprintf fmt "@[<hov 2>for(%a; %a; %a) {@\n%a@]@\n}"
	pp_instruction i1 pp_pexpr e pp_instruction i2 aux b
    | For _ -> assert false (* not used by the translation *)
    | Block b ->
      if b <> [] then
	Format.fprintf fmt "@[<hov 2>{@\n%a@]@\n}" aux b
  end;
  if line_break then Format.fprintf fmt "@\n"

let pp_insertion_lb = pp_insertion ~line_break:true
let pp_insertion_nlb = pp_insertion ~line_break:false

class print_insertions insertions ~print_label () = object(self)
  inherit Printer.extensible_printer () as super

  val mutable current_function = None

  method private fundecl fmt f =
    let was_ghost = is_ghost in
    let entry_point_name=Kernel_function.get_name(fst(Globals.entry_point())) in
    let entering_ghost = f.svar.vghost && not was_ghost in
    (* BEGIN precond (entry-point) *)
    if f.svar.vname = entry_point_name then
      begin
	let precond = f.svar.vname ^ "_precond" in
	let x,y,z =
	  match f.svar.vtype with TFun(_,x,y,z) -> x,y,z | _ -> assert false
	in
	Format.fprintf fmt "%a@ @[<hov 2>{@\n"
	  (self#typ (Some (fun fmt -> Format.fprintf fmt "%s" precond)))
	  (TFun(Cil.intType,x,y,z));
	begin
	  try
	    let q = Hashtbl.find insertions (BegFunc precond) in
	    Queue.iter
	      (fun s ->
		if print_label then
		  Format.fprintf fmt "/* BegFunc %s */ " precond;
		Format.fprintf fmt "%a" pp_insertion_lb s) q
	  with _ -> ()
	end;
	Format.fprintf fmt "@[return 1;@]";
	Format.fprintf fmt "@]@\n}@\n@\n"
      end;
    (* END precond (entry-point) *)
    Format.fprintf fmt "@[%t%a@\n@[<v 2>"
      (if entering_ghost then fun fmt -> Format.fprintf fmt "/*@@ ghost@ " 
       else ignore)
      self#vdecl f.svar;
    (* body. *)
    if entering_ghost then is_ghost <- true;
    Format.fprintf fmt "@[<hov 2>{@\n";
    begin
      try
	let q = Hashtbl.find insertions (BegFunc f.svar.vname) in
	Queue.iter
	  (fun s ->
	    if print_label then
	      Format.fprintf fmt "/* BegFunc %s */ " f.svar.vname;
	    Format.fprintf fmt "%a" pp_insertion_lb s) q
      with _ -> ()
    end;
    self#block ~braces:true fmt f.sbody;
    (* EndFunc not necessary here ? *)
    Format.fprintf fmt "@.}";
    if entering_ghost then is_ghost <- false;
    Format.fprintf fmt "@]%t@]@."
      (if entering_ghost then fun fmt -> Format.fprintf fmt "@ */" else ignore)
  (* end of fundecl *)

  method! private annotated_stmt next fmt stmt =
    Format.pp_open_hvbox fmt 2;
    self#stmt_labels fmt stmt;
    Format.pp_open_hvbox fmt 0;
    let kf = Kernel_function.find_englobing_kf stmt in
    let beg_stmt =
      try Hashtbl.find insertions (BegStmt stmt.sid) with _ -> Queue.create() in
    let end_stmt =
      try Hashtbl.find insertions (EndStmt stmt.sid) with _ -> Queue.create() in
    if not (Queue.is_empty beg_stmt) || not(Queue.is_empty end_stmt) then
      Format.fprintf fmt "@[<hov 2>{@\n";
    Queue.iter
      (fun s ->
	if print_label then
	  Format.fprintf fmt "/* BegStmt %i */ " stmt.sid;
	Format.fprintf fmt "%a" pp_insertion_lb s) beg_stmt;
    begin
      match stmt.skind with
      | Loop(_,b,l,_,_) ->
	Format.fprintf fmt "%a@[<v 2>while (1) {@\n"
	  (fun fmt -> self#line_directive fmt) l;
	begin
	  try
	    let q = Hashtbl.find insertions (BegIter stmt.sid) in
	    Queue.iter
	      (fun s ->
		if print_label then
		  Format.fprintf fmt "/* BegIter %i */ " stmt.sid;
		Format.fprintf fmt "%a" pp_insertion_lb s) q
	  with _ -> ()
	end;
	Format.fprintf fmt "%a" (fun fmt -> self#block fmt) b;
	begin
	  try
	    let q = Hashtbl.find insertions (EndIter stmt.sid) in
	    Queue.iter
	      (fun s ->
		if print_label then
		  Format.fprintf fmt "/* EndIter %i */ " stmt.sid;
		Format.fprintf fmt "%a" pp_insertion_lb s) q
	  with _ -> ()
	end;
	Format.fprintf fmt "}@\n @]"
      | Return _ ->
	let f = Kernel_function.get_name kf in
	begin
	  try
	    let q = Hashtbl.find insertions (EndFunc f) in
	    Queue.iter
	      (fun s ->
		if print_label then
		  Format.fprintf fmt "/* EndFunc %s */ " f;
		Format.fprintf fmt "%a" pp_insertion_lb s) q
	  with _ -> ()
	end;
	self#stmtkind next fmt stmt.skind
      | _ -> self#stmtkind next fmt stmt.skind
    end;
    Queue.iter
      (fun s ->
	if print_label then
	  Format.fprintf fmt "/* EndStmt %i */ " stmt.sid;
	Format.fprintf fmt "%a" pp_insertion_lb s) end_stmt;
    if not(Queue.is_empty beg_stmt) || not(Queue.is_empty end_stmt) then
      Format.fprintf fmt "@]@\n}";
    Format.pp_close_box fmt ();
    Format.pp_close_box fmt ()
  (* end of annotated_stmt *)

  method! file fmt f =
    Format.fprintf fmt "@[/* Generated by Frama-C */@\n" ;
    Format.fprintf fmt "#include <gmp.h>@\n";
    Format.fprintf fmt "extern int pathcrawler_assert_exception(char*,int);@\n";
    Format.fprintf fmt "extern int pathcrawler_dimension(void*);@\n";
    Format.fprintf fmt "extern void pathcrawler_to_framac(char*);@\n";
    Format.fprintf fmt "extern void* malloc(unsigned);@\n";
    Format.fprintf fmt "extern void free(void*);@\n";
    Cil.iterGlobals f (fun g -> self#global fmt g);
    Format.fprintf fmt "@]@."

  (* unmodified *)
  method private vdecl_complete fmt v =
    let display_ghost = v.vghost && not is_ghost in
    Format.fprintf fmt "@[<hov 0>%t%a;%t@]"
      (if display_ghost then fun fmt -> Format.fprintf fmt "/*@@ ghost@ "
       else ignore)
      self#vdecl v
      (if display_ghost then fun fmt -> Format.fprintf fmt "@ */" else ignore)
  
  (* unmodified *)
  method private in_current_function vi =
    assert (current_function = None);
    current_function <- Some vi

  (* unmodified *)
  method private out_current_function =
    assert (current_function <> None);
    current_function <- None

  method! global fmt g =
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
    | GVarDecl (_, vi, _) -> if print_var vi then super#global fmt g
    | _ -> super#global fmt g
  (* end of global *)
end
