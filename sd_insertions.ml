
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
| Cmp of relation * ctype_expr * ctype_expr
| Gmp_cmp of binop * gmp_expr * gmp_expr
| Gmp_cmp_ui of binop * gmp_expr * ctype_expr
| Gmp_cmp_si of binop * gmp_expr * ctype_expr
| Gmp_cmpr of relation * gmp_expr * gmp_expr
| Gmp_cmpr_ui of relation * gmp_expr * ctype_expr
| Gmp_cmpr_si of relation * gmp_expr * ctype_expr
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

and fragment =
| Gmp_fragment of gmp_expr
| Ctype_fragment of ctype_expr

and instruction =
| Affect of ctype_expr * ctype_expr
| Free of ctype_expr
| Pc_to_framac of string
| Pc_assert_exn of string * int
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
| If_cond of ctype_expr
| Else_cond
| For of instruction option * ctype_expr option * instruction option
| Block_open
| Block_close


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
    self#insert (Decl_gmp_var var);
    Declared_gmp_var var

  method private init_gmp_var var =
    self#insert (Instru(Gmp_init var));
    Initialized_gmp_var var

  method private init_set_gmp_var var v =
    self#insert (Instru(Gmp_init_set (var, v)));
    Initialized_gmp_var var

  method private init_set_si_gmp_var var v =
    self#insert (Instru(Gmp_init_set_si (var, v)));
    Initialized_gmp_var var

  method private init_set_ui_gmp_var var v =
    self#insert (Instru(Gmp_init_set_ui (var, v)));
    Initialized_gmp_var var

  method private init_set_str_gmp_var var v =
    self#insert (Instru(Gmp_init_set_str (var, v)));
    Initialized_gmp_var var

  method private fresh_ctype_var ty =
    last_ctype_var_id <- last_ctype_var_id + 1;
    Fresh_ctype_var (last_ctype_var_id, ty)

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
	begin
	  let prefix =
	    match v.lv_type with
	    | Ctype ty
		when (Cil.isPointerType ty || Cil.isArrayType ty) && in_old_ptr ->
	      "old_ptr"
	    | _ -> "old"
	  in
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

  method private term t : fragment =
    self#term_node t

  method private gmp_fragment = function
  | Gmp_fragment x -> x
  | Ctype_fragment _ -> assert false

  method private ctype_fragment = function
  | Ctype_fragment x -> x
  | Gmp_fragment _ -> assert false

  method private lambda li lower upper _q t =
    let builtin_name = li.l_var_info.lv_name in
    let init_val = match builtin_name with
      | s when s = "\\sum" -> Zero
      | s when s = "\\product" -> One
      | s when s = "\\numof" -> Zero
      | _ -> assert false (* unreachable *)
    in
    let fresh_var = self#fresh_gmp_var() in
    let decl_var = self#decl_gmp_var fresh_var in
    let init_var = self#init_set_si_gmp_var decl_var init_val in
    self#insert Block_open;
    let low = self#term lower in
    let up = self#term upper in
    begin
      match lower.term_type with
      | Linteger ->
	begin
	  match upper.term_type with
	  | Linteger ->
	    let fresh_iter = self#fresh_gmp_var() in
	    let decl_iter = self#decl_gmp_var fresh_iter in
	    let init_iter =
	      self#init_set_gmp_var decl_iter (self#gmp_fragment low) in
	    self#insert(For(None, Some(Gmp_cmp(Le, init_iter,
					      self#gmp_fragment up)), None));
	    self#insert Block_open;
	    let lambda_term = self#term t in
	    begin
	      match builtin_name with
	      | s when s = "\\sum" ->
		self#insert (Instru(Gmp_binop(PlusA, init_var,
					      init_var,
					      self#gmp_fragment lambda_term)));
	      | s when s = "\\product" ->
		self#insert (Instru(Gmp_binop(Mult, init_var,
					      init_var,
					      self#gmp_fragment lambda_term)));
	      | s when s = "\\numof" ->
		(* lambda_term is of type:
		   Ltype (lt,_) when lt.lt_name = Utf8_logic.boolean *)
		self#insert (If_cond(self#ctype_fragment lambda_term));
		self#insert (Instru(Gmp_binop_ui(PlusA, init_var,
						 init_var, One)));
	      | _ -> assert false
	    end;
	    self#insert (Instru(Gmp_binop_ui(PlusA,init_iter,init_iter, One)));
	    if builtin_name <> "\\numof" then
	      self#insert (Instru(Gmp_clear(self#gmp_fragment lambda_term)));
	    self#insert Block_close;
	    self#insert (Instru(Gmp_clear init_iter));
	    self#insert (Instru(Gmp_clear(self#gmp_fragment low)));
	    self#insert (Instru(Gmp_clear(self#gmp_fragment up)));
	    self#insert Block_close;
	    Gmp_fragment init_var
	  | Lreal -> assert false (* unreachable *)
	  | _ -> assert false (* unreachable ? *)
	end
      | Lreal -> assert false (* unreachable *)
      | _ -> assert false (* unreachable ? *)
    end

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
	  let decl_var = self#decl_gmp_var fresh_var in
	  let str = Pretty_utils.sfprintf "%a" Printer.pp_term t in
	  let init_var = self#init_set_str_gmp_var decl_var str in
	  Gmp_fragment init_var
	| Lreal -> assert false (* TODO: reals *)
	| _ -> Ctype_fragment(Cst(Pretty_utils.sfprintf "%a" Printer.pp_term t))
      end

    | TLval tlval ->
      begin
	match ty with
	| Linteger ->
	  let fresh_var = self#fresh_gmp_var() in
	  let t' = self#gmp_fragment (self#tlval tlval) in
	  let decl_var = self#decl_gmp_var fresh_var in
	  let init_var = self#init_set_gmp_var decl_var t' in
	  Gmp_fragment init_var
	| Lreal -> assert false (* TODO: reals *)
	| _ -> self#tlval tlval
      end

    | TSizeOf _
    | TSizeOfE _
    | TSizeOfStr _
    | TAlignOf _
    | TAlignOfE _ ->
      (*Pretty_utils.sfprintf "%a" Printer.pp_term t*)
      assert false (* TODO ? *)

    | TUnOp(op, t') ->
      begin
	match ty with
	| Linteger ->
	  assert(op = Neg);
	  let x = self#term t' in
	  let fresh_var = self#fresh_gmp_var() in
	  let decl_var = self#decl_gmp_var fresh_var in
	  let init_var = self#init_gmp_var decl_var in
	  begin
	    match t'.term_type with
	    | Linteger ->
	      self#insert
		(Instru(Gmp_ui_sub(init_var,Zero,self#gmp_fragment x)));
	      self#insert (Instru(Gmp_clear(self#gmp_fragment x)))
	    | Lreal -> assert false (* unreachable *)
	    | Ctype(TInt((IULongLong|IULong|IUShort|IUInt|IUChar),_)) ->
	      let fresh_var' = self#fresh_gmp_var() in
	      let decl_var' = self#decl_gmp_var fresh_var' in
	      let init_var' =
		self#init_set_ui_gmp_var decl_var' (self#ctype_fragment x) in
	      self#insert (Instru(Gmp_ui_sub(init_var', Zero,init_var')));
	      self#insert (Instru(Gmp_clear init_var'))
	    | Ctype(TInt _) ->
	      let fresh_var' = self#fresh_gmp_var() in
	      let decl_var' = self#decl_gmp_var fresh_var' in
	      let init_var' =
		self#init_set_si_gmp_var decl_var' (self#ctype_fragment x) in
	      self#insert (Instru(Gmp_ui_sub(init_var', Zero, init_var')));
	      self#insert (Instru(Gmp_clear init_var'));
	    | _ -> assert false (* unreachable *)
	  end;
	  Gmp_fragment init_var
	| Lreal -> assert false (* TODO: reals *)
	| _ ->
	  let x = self#ctype_fragment (self#term t') in
	  Ctype_fragment (Unop(op, x))
      end

    | TBinOp((IndexPI|PlusPI|MinusPI) as op, t1, t2) ->
      begin
	match t2.term_type with
	| Linteger ->
	  let x = self#ctype_fragment (self#term t1)
	  and y = self#gmp_fragment (self#term t2) in
	  let var = self#fresh_ctype_var Cil.intType in
	  self#insert (Decl_ctype_var var);
	  self#insert (Instru(Affect(var, Gmp_get_si y)));
	  self#insert (Instru(Gmp_clear y));
	  Ctype_fragment (Binop(op, x, var))
	| Lreal -> assert false (* unreachable *)
	| _ ->
	  let x = self#ctype_fragment (self#term t1)
	  and y = self#ctype_fragment (self#term t2) in
	  Ctype_fragment (Binop(op, x, y))
      end

    | TBinOp(op, t1, t2) ->
      begin
	match ty with
	| Linteger ->
	  let x = self#term t1 and y = self#term t2 in
	  let fresh_var = self#fresh_gmp_var() in
	  let decl_var = self#decl_gmp_var fresh_var in
	  let init_var = self#init_gmp_var decl_var in
	  begin
	    match t1.term_type, t2.term_type with
	    | Linteger, Linteger ->
	      self#insert (Instru(Gmp_binop(op, init_var, self#gmp_fragment x,
					    self#gmp_fragment y)));
	      self#insert (Instru(Gmp_clear(self#gmp_fragment x)));
	      self#insert (Instru(Gmp_clear(self#gmp_fragment y)));
	      Gmp_fragment init_var
	    | Linteger,Ctype(TInt((IULongLong|IULong|IUShort|IUInt|IUChar),_))->
	      self#insert (Instru(Gmp_binop_ui(op, init_var,self#gmp_fragment x,
					       self#ctype_fragment y)));
	      self#insert (Instru(Gmp_clear(self#gmp_fragment x)));
	      Gmp_fragment init_var
	    | Linteger, Ctype (TInt _) ->
	      self#insert (Instru(Gmp_binop_si(op, init_var,self#gmp_fragment x,
					       self#ctype_fragment y)));
	      self#insert (Instru(Gmp_clear(self#gmp_fragment x)));
	      Gmp_fragment init_var
	    | Ctype(TInt((IULongLong|IULong|IUShort|IUInt|IUChar),_)),Linteger->
	      if op = PlusA || op = Mult then
		begin
		  self#insert (Instru(Gmp_binop_ui(op, init_var,
						   self#gmp_fragment y,
						   self#ctype_fragment x)));
		  self#insert (Instru(Gmp_clear(self#gmp_fragment y)));
		  Gmp_fragment init_var
		end
	      else
		assert false (* TODO *)
	    | Ctype (TInt _), Linteger ->
	      if op = PlusA || op = Mult then
		begin
		  self#insert (Instru(Gmp_binop_si(op, init_var,
						   self#gmp_fragment y,
						   self#ctype_fragment x)));
		  self#insert (Instru(Gmp_clear(self#gmp_fragment y)));
		  Gmp_fragment init_var
		end
	      else
		assert false (* TODO *)
	    | Ctype(TInt _), Ctype(TInt _) ->
	      let fresh_var1 = self#fresh_gmp_var() in
	      let decl_var1 = self#decl_gmp_var fresh_var1 in
	      let fresh_var2 = self#fresh_gmp_var() in
	      let decl_var2 = self#decl_gmp_var fresh_var2 in
	      let init_var1 =
		self#init_set_si_gmp_var decl_var1 (self#ctype_fragment x) in
	      let init_var2 =
		self#init_set_si_gmp_var decl_var2 (self#ctype_fragment y) in
	      self#insert (Instru(Gmp_binop(op,init_var,init_var1,init_var2)));
	      self#insert (Instru(Gmp_clear init_var1));
	      self#insert (Instru(Gmp_clear init_var2));
	      Gmp_fragment init_var
	    | _ -> assert false
	  end
	| Lreal -> assert false (* TODO: reals *)
	| Ltype (lt,_) when lt.lt_name = Utf8_logic.boolean ->
	  begin
	    match t1.term_type, t2.term_type with
	    | Linteger, Linteger ->
	      let var = self#fresh_ctype_var Cil.intType in
	      let x = self#term t1 in
	      let y = self#term t2 in
	      self#insert (Decl_ctype_var var);
	      self#insert (Instru(Affect(var, Gmp_cmp(op, self#gmp_fragment x,
						      self#gmp_fragment y))));
	      self#insert (Instru(Gmp_clear(self#gmp_fragment x)));
	      self#insert (Instru(Gmp_clear(self#gmp_fragment y)));
	      Ctype_fragment var
	    | _ ->
	      let x = self#ctype_fragment (self#term t1) in
	      let y = self#ctype_fragment (self#term t2) in
	      Ctype_fragment (Binop(op, x, y))
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
	      let v = self#gmp_fragment (self#term t') in
	      let var = self#fresh_ctype_var ty' in
	      self#insert (Decl_ctype_var var);
	      self#insert (Instru(Affect(var, Gmp_get_ui v)));
	      self#insert (Instru(Gmp_clear v));
	      Ctype_fragment var
	    | Ctype (TInt _) ->
	      let v = self#gmp_fragment (self#term t') in
	      let var = self#fresh_ctype_var ty' in
	      self#insert (Decl_ctype_var var);
	      self#insert (Instru(Affect(var, Gmp_get_si v)));
	      self#insert (Instru(Gmp_clear v));
	      Ctype_fragment var
	    | _ -> assert false (* unreachable *)
	  end
	| Lreal -> assert false (* reals *)
	| Ctype _ ->
	  let v = self#ctype_fragment (self#term t') in
	  Ctype_fragment (Cast (ty', v))
	| _ -> assert false (* unreachable *)
      end

    | TAddrOf _
    | TStartOf _ ->
      (*Pretty_utils.sfprintf "%a" Printer.pp_term t*)
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
	      let x = self#gmp_fragment (self#term param) in
	      let fresh_var = self#fresh_gmp_var() in
	      let decl_var = self#decl_gmp_var fresh_var in
	      let init_var = self#init_gmp_var decl_var in
	      self#insert (Instru(Gmp_abs(init_var, x)));
	      self#insert (Instru(Gmp_clear x));
	      Gmp_fragment init_var
	    end
	  else
	    if builtin_name = "\\min" || builtin_name = "\\max" ||
	      builtin_name = "\\sum" || builtin_name = "\\product" ||
	      builtin_name = "\\numof" then
	      begin
		match params with
		| [lower;upper;{term_node=Tlambda([q],t)}] ->
		  self#lambda li lower upper q t
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
	  let fresh_var = self#fresh_gmp_var() in
	  let decl_var = self#decl_gmp_var fresh_var in
	  let init_var = self#init_gmp_var decl_var in
	  let cond' = self#gmp_fragment (self#term cond) in
	  self#insert (If_cond(Gmp_cmp_si(Ne, cond', Zero)));
	  self#insert Block_open;
	  let then_b' = self#gmp_fragment (self#term then_b) in
	  self#insert (Instru(Gmp_set(init_var, then_b')));
	  self#insert (Instru(Gmp_clear(then_b')));
	  self#insert Block_close;
	  self#insert Else_cond;
	  self#insert Block_open;
	  let else_b' = self#gmp_fragment (self#term else_b) in
	  self#insert (Instru(Gmp_set(init_var, else_b')));
	  self#insert (Instru(Gmp_clear(else_b')));
	  self#insert Block_close;
	  self#insert (Instru(Gmp_clear(cond')));
	  Gmp_fragment init_var
	| Lreal -> assert false (* TODO: reals *)
	| _ -> assert false (* unreachable *)
      end
    
    | Tat(_, StmtLabel _) ->
      if current_function <> None then
	Sd_options.Self.warning "%a unsupported" Printer.pp_term t;
      (*Pretty_utils.sfprintf "%a" Printer.pp_term t*)
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
	    (*Pretty_utils.sfprintf "%a" Printer.pp_term t*)
	    assert false (* TODO ? *)
	  end

    | Tbase_addr _ -> Sd_options.Self.not_yet_implemented "Tbase_addr"
    | Toffset _ -> Sd_options.Self.not_yet_implemented "Toffset"
    | Tblock_length _ -> Sd_options.Self.not_yet_implemented "Tblock_length"
    | Tnull -> Ctype_fragment Zero

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
	      let v = self#ctype_fragment (self#term t') in
	      let fresh_var = self#fresh_gmp_var() in
	      let decl_var = self#decl_gmp_var fresh_var in
	      let init_var = self#init_set_ui_gmp_var decl_var v in
	      Gmp_fragment init_var
	    | Ctype(TInt _) | Ctype(TEnum _) ->
	      let v = self#ctype_fragment (self#term t') in
	      let fresh_var = self#fresh_gmp_var() in
	      let decl_var = self#decl_gmp_var fresh_var in
	      let init_var = self#init_set_si_gmp_var decl_var v in
	      Gmp_fragment init_var
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
	  let v = self#gmp_fragment (self#term t') in
	  let var = self#fresh_ctype_var ty' in
	  self#insert (Decl_ctype_var var);
	  begin
	    match ty' with
	    | TInt((IULongLong|IULong|IUShort|IUInt|IUChar),_) ->
	      self#insert (Instru(Affect(var,Gmp_get_ui v)));
	    | TInt _ ->
	      self#insert (Instru(Affect(var,Gmp_get_si v)));
	    | _ -> assert false
	  end;
	  self#insert (Instru(Gmp_clear v));
	  Ctype_fragment var
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
  (*end term*)

  method private tlval (tlhost, toffset) =
    match tlhost with
    | TResult _ ->
      let var = Extlib.the result_varinfo in
      Ctype_fragment (My_ctype_var(var.vtype, var.vname))
    | _ ->
      let lhost = self#tlhost tlhost in
      let rec aux ret = function
	| TNoOffset -> ret
	| TField (fi, tof) -> aux (Field(ret, fi.fname)) tof
	| TModel _ -> assert false (* TODO *)
	| TIndex (t, tof) ->
	  let t' = self#term t in
	  begin
	    match t.term_type with
	    | Linteger -> aux (Index(ret, Gmp_get_si(self#gmp_fragment t'))) tof
	    | Lreal -> assert false (* unreachable *)
	    | _ -> aux (Index(ret, self#ctype_fragment t')) tof
	  end
      in
      match lhost with
      | Gmp_fragment _ -> (* TODO *) assert (toffset = TNoOffset); lhost
      | Ctype_fragment lhost' -> Ctype_fragment (aux lhost' toffset)

  method private tlhost lhost =
    match lhost with
    | TVar lv -> self#logic_var lv
    | TResult _ -> assert false
    | TMem t -> Ctype_fragment (Deref (self#ctype_fragment (self#term t)))

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
    let entry_point_name =
      Kernel_function.get_name (fst(Globals.entry_point())) in
    let kf = Globals.Functions.find_by_name f.svar.vname in
    (*let loc = Kernel_function.get_location kf in*)
    let behaviors = Annotations.behaviors kf in
    self#compute_result_varinfo f;

    (* BEGIN precond (entry-point) *)
    if f.svar.vname = entry_point_name then
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
	  (* TODO: add an option to translate anyway? (deleting the filter) *)
	  let preconds = List.filter not_translated preconds in
	  let do_precond p =
	    let v = self#predicate(self#subst_pred p.ip_content) in
	    if v <> One then (* '1' is for untreated predicates *)
	      begin
		self#insert (If_cond(Unop(LNot, v)));
		self#insert (Instru(Ret Zero))
	      end
	  in
	  if preconds <> [] then
	    begin
	      self#bhv_assumes_begin b;
	      List.iter do_precond preconds;
	      self#bhv_assumes_end b
	    end
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
	    self#pc_assert_exception
	      pred.ip_content "Pre-condition!" id prop
	  in
	  if pre <> [] then
	    begin
	      self#bhv_assumes_begin b;
	      List.iter do_precond pre;
	      self#bhv_assumes_end b
	    end
	) behaviors
      end;
    (* END precond (not entry-point) *)

    current_label <- Some (EndFunc f.svar.vname);

    (* BEGIN postcond *)
    if (self#at_least_one_prop kf behaviors)
      || (Sd_options.Behavior_Reachability.get()) then
      begin
	self#insert Block_open;
	List.iter (fun b ->
	  let post = b.b_post_cond in
	  let to_prop = Property.ip_of_ensures kf Kglobal b in
	  let post = List.filter (fun x -> List.mem (to_prop x) props) post in
	  let do_postcond (tk,pred) =
	    let prop = to_prop (tk,pred) in
	    let id = Sd_utils.to_id prop in
	    self#pc_assert_exception
	      pred.ip_content "Post-condition!" id prop
	  in
	  if post <> [] || (Sd_options.Behavior_Reachability.get()) then
	    begin
	      self#bhv_assumes_begin b;
	      if not (Cil.is_default_behavior b)
		&& (Sd_options.Behavior_Reachability.get()) then
		begin
		  let str =
		    Format.sprintf "@@FC:REACHABLE_BHV:%i" bhv_to_reach_cpt in
		  self#insert (Instru(Pc_to_framac str));
		  Sd_states.Behavior_Reachability.replace
		    bhv_to_reach_cpt
		    (kf, b, false);
		  bhv_to_reach_cpt <- bhv_to_reach_cpt+1
		end;
	      List.iter do_postcond post;
	      self#bhv_assumes_end b
	    end
	) behaviors;
	self#insert Block_close
      end;
    (* END postcond *)

    current_label <- Some (BegFunc f.svar.vname);

    (* alloc variables for \at terms *)
    let concat_indice str ind = str ^ "[" ^ ind ^ "]" in
    let rec array_to_ptr = function
      | TArray(ty,_,_,attributes) -> TPtr(array_to_ptr ty, attributes)
      | x -> x
    in
    let array_to_ptr x = array_to_ptr (Cil.unrollTypeDeep x) in
    let dig_type = function
      | TPtr(ty,_) | TArray(ty,_,_,_) -> ty
      | ty -> Sd_options.Self.abort "dig_type %a" Printer.pp_typ ty
    in
    let dig_type x = dig_type (Cil.unrollTypeDeep x) in
    let iter_counter = ref 0 in
    let lengths = Sd_utils.lengths_from_requires kf in
    let do_varinfo v =
      let terms =
	try Cil_datatype.Varinfo.Hashtbl.find lengths v
	with Not_found -> []
      in
      let my_v = My_ctype_var((array_to_ptr v.vtype), v.vname) in
      let my_old_v = My_ctype_var((array_to_ptr v.vtype), "old_"^v.vname) in
      self#insert (Decl_ctype_var my_old_v);
      self#insert (Instru(Affect(my_old_v, my_v)));
      let rec alloc_aux indices ty = function
	| h :: t ->
	  let all_indices = List.fold_left concat_indice "" indices in
	  let old_ty = ty in
	  let ty = dig_type ty in
	  let h' = self#term h in
	  let iterator = "__stady_iter_" ^ (string_of_int !iter_counter) in
	  let my_iterator = My_ctype_var(Cil.intType, iterator) in
	  self#insert (Decl_ctype_var my_iterator);
	  begin
	    match h.term_type with
	    | Linteger ->
	      let my_old_ptr =
		My_ctype_var(old_ty, "old_ptr_"^v.vname^all_indices) in
	      let h' = self#gmp_fragment h' in
	      self#insert (Instru(Affect(my_old_ptr,
					 Malloc(Binop(Mult,(Gmp_get_si h'),
						      Sizeof ty)))));
	      self#insert (For(
		(Some(Affect(my_iterator, Zero))),
		(Some(Binop(Lt, my_iterator, Gmp_get_si h'))),
		(Some(Affect(my_iterator, (Binop(PlusA, my_iterator, One)))))
	      ));
	      self#insert Block_open;
	      iter_counter := !iter_counter + 1;
	      alloc_aux (Sd_utils.append_end indices iterator) ty t;
	      self#insert Block_close;
	      self#insert (Instru(Gmp_clear h'))
	    | Lreal -> assert false (* TODO: reals *)
	    | _ ->
	      let my_old_ptr =
		My_ctype_var(old_ty, "old_ptr_"^v.vname^all_indices) in
	      let h' = self#ctype_fragment h' in
	      self#insert (Instru(Affect(my_old_ptr,
					 Malloc(Binop(Mult,h',
						      Sizeof ty)))));
	      self#insert (For(
		(Some(Affect(my_iterator, Zero))),
		(Some(Binop(Lt, my_iterator, h'))),
		(Some(Affect(my_iterator, (Binop(PlusA, my_iterator, One)))))
	      ));
	      self#insert Block_open;
	      iter_counter := !iter_counter + 1;
	      alloc_aux (Sd_utils.append_end indices iterator) ty t;
	      self#insert Block_close
	  end
	| [] ->
	  let all_indices = List.fold_left concat_indice "" indices in
	  let my_old_ptr =
	    My_ctype_var(ty, "old_ptr_"^v.vname^all_indices) in
	  let my_var = My_ctype_var (ty, v.vname^all_indices) in
	  self#insert (Instru(Affect(my_old_ptr, my_var)))
      in
      if Cil.isPointerType v.vtype || Cil.isArrayType v.vtype then
	begin
	  let my_old_ptr =
	    My_ctype_var((array_to_ptr v.vtype), "old_ptr_"^v.vname) in
	  self#insert (Decl_ctype_var my_old_ptr);
	  alloc_aux [] v.vtype terms
	end
    in
    List.iter do_varinfo visited_globals;
    List.iter do_varinfo (Kernel_function.get_formals kf);

    current_label <- Some (EndFunc f.svar.vname);

    (* dealloc variables for \at terms *)
    begin
      try
	let iter_counter = ref 0 in
	let lengths = Sd_utils.lengths_from_requires kf in
	let do_varinfo v =
	  let terms =
	    try Cil_datatype.Varinfo.Hashtbl.find lengths v
	    with Not_found -> []
	  in
	  let rec dealloc_aux indices = function
	    | [] -> ()
	    | _ :: [] ->
	      let all_indices = List.fold_left concat_indice "" indices in
	      let my_old_ptr =
		My_ctype_var(Cil.voidPtrType, "old_ptr_"^v.vname^all_indices) in
	      self#insert (Instru(Free(my_old_ptr)))
	    | h :: t ->
	      let iterator = "__stady_iter_"^(string_of_int !iter_counter) in
	      let my_iterator = My_ctype_var(Cil.intType, iterator) in
	      self#insert (Decl_ctype_var my_iterator);
	      let h' = self#term h in
	      let all_indices = List.fold_left concat_indice "" indices in
	      iter_counter := !iter_counter + 1;
	      let indices = Sd_utils.append_end indices iterator in
	      begin
		match h.term_type with
		| Linteger ->
		  let h' = self#gmp_fragment h' in
		  self#insert (For(
		    (Some(Affect(my_iterator, Zero))),
		    (Some(Binop(Lt, my_iterator, Gmp_get_si h'))),
		    (Some(Affect(my_iterator, (Binop(PlusA, my_iterator,One)))))
		  ));
		  self#insert Block_open;
		  dealloc_aux indices t;
		  self#insert Block_close;
		  self#insert (Instru(Gmp_clear h'))
		| Lreal -> assert false (* TODO: reals *)
		| _ ->
		  let h' = self#ctype_fragment h' in
		  self#insert (For(
		    (Some(Affect(my_iterator, Zero))),
		    (Some(Binop(Lt, my_iterator, h'))),
		    (Some(Affect(my_iterator, (Binop(PlusA, my_iterator,One)))))
		  ));
		  self#insert Block_open;
		  dealloc_aux indices t;
		  self#insert Block_close
	      end;
	      let my_old_ptr =
		My_ctype_var(Cil.voidPtrType, "old_ptr_"^v.vname^all_indices) in
	      self#insert (Instru(Free(my_old_ptr)))
	  in
	  dealloc_aux [] terms
	in
	List.iter do_varinfo visited_globals;
	List.iter do_varinfo (Kernel_function.get_formals kf)
      with Not_found -> ()
    end;

    current_label <- None;

    Cil.DoChildren
  (*end vfunc*)

  method private subst_pred p = (new Sd_subst.subst)#subst_pred p [] [] [] []

  method private bhv_assumes_begin bhv =
    if bhv.b_assumes <> [] then
      let f a = self#predicate (self#subst_pred a.ip_content) in
      let vars = List.map f bhv.b_assumes in
      let rec aux ret = function
	| [] -> ret
	| h :: t -> aux (Binop(LAnd, ret, h)) t
      in
      let exp = aux One vars in 
      self#insert (If_cond exp);
      self#insert Block_open
	
  method private bhv_assumes_end bhv =
    if bhv.b_assumes <> [] then
      self#insert Block_close

  method private pc_assert_exception pred msg id prop =
    let var = self#predicate (self#subst_pred pred) in
    self#insert (If_cond(Unop(LNot, var)));
    self#insert (Instru(Pc_assert_exn(msg, id)));
    translated_properties <- prop :: translated_properties

  method private bhv_guard_begin behaviors =
    if behaviors <> [] then
      let f a = self#predicate (self#subst_pred a.ip_content) in
      let g assumes_list = List.map f assumes_list in
      let vars = List.map g behaviors in
      let rec aux' ret = function
	| [] -> ret
	| h :: t -> aux' (Binop(LAnd, ret, h)) t
      in
      let rec aux ret = function
	| [] -> ret
	| h :: t -> aux (Binop(LOr, ret, aux' One h)) t
      in
      let exp = aux Zero vars in
      self#insert (If_cond exp);
      self#insert Block_open

  method private bhv_guard_end behaviors =
    if behaviors <> [] then
      self#insert Block_close

  method! vcode_annot ca =
    let stmt = Extlib.the self#current_stmt in
    let kf = Kernel_function.find_englobing_kf stmt in
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
    begin
      match ca.annot_content with
      | AStmtSpec (_,bhvs) ->
	
	current_label <- Some (BegStmt stmt.sid);

	self#bhv_guard_begin behaviors;
	List.iter (fun b ->
	  let pre = b.b_requires in
	  let to_prop = Property.ip_of_requires kf (Kstmt stmt) b in
	  let pre = List.filter (fun p -> List.mem (to_prop p) props) pre in
	  let do_precond pred =
	    let prop = to_prop pred in
	    let id = Sd_utils.to_id prop in
	    self#pc_assert_exception pred.ip_content
	      "Stmt Pre-condition!" id prop
	  in
	  if pre <> [] then
	    begin
	      self#bhv_assumes_begin b;
	      List.iter do_precond pre;
	      self#bhv_assumes_end b
	    end
	) bhvs.spec_behavior;
	self#bhv_guard_end behaviors;

	current_label <- Some (EndStmt stmt.sid);
	
	if self#at_least_one_prop kf bhvs.spec_behavior then
	  begin
	    self#bhv_guard_begin behaviors;
	    self#insert Block_open;
	    List.iter (fun b ->
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
		begin
		  self#bhv_assumes_begin b;
		  List.iter do_postcond post;
		  self#bhv_assumes_end b
		end
	    ) bhvs.spec_behavior;
	    self#insert Block_close;
	    self#bhv_guard_end behaviors
	  end;

	current_label <- None

      | AAssert (_,pred) ->

	current_label <- Some (BegStmt stmt.sid);

	let prop = Property.ip_of_code_annot_single kf stmt ca in
	if List.mem prop props then
	  begin
	    let id = Sd_utils.to_id prop in
	    self#bhv_guard_begin behaviors;
	    self#pc_assert_exception pred.content "Assert!" id prop;
	    self#bhv_guard_end behaviors
	  end;

	current_label <- None

      | AInvariant (_,true,pred) ->

	let prop = Property.ip_of_code_annot_single kf stmt ca in
	if List.mem prop props then
	  let id = Sd_utils.to_id prop in
	  let f msg =
	    self#bhv_guard_begin behaviors;
	    self#pc_assert_exception pred.content msg id prop;
	    self#bhv_guard_end behaviors
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
	      let term' = self#gmp_fragment (self#term term) in
	      self#insert (If_cond (Gmp_cmp_ui(Lt, term', Zero)));
	      self#insert (Instru(Pc_assert_exn("Variant non positive", id)));
	      current_label <- Some (EndStmt stmt.sid);
	      self#insert (Instru(Gmp_clear(term')));
	      current_label <- Some (BegIter stmt.sid);
	      let term' = self#gmp_fragment (self#term term) in
	      let fresh_variant = self#fresh_gmp_var() in
	      let decl_variant = self#decl_gmp_var fresh_variant in
	      let init_variant = self#init_set_gmp_var decl_variant term' in
	      current_label <- Some (EndIter stmt.sid);
	      let term' = self#gmp_fragment (self#term term) in
	      self#insert (If_cond(Gmp_cmp_ui(Lt, init_variant, Zero)));
	      self#insert (Instru(Pc_assert_exn("Variant non positive", id)));
	      self#insert (If_cond(Gmp_cmp(Ge, term', init_variant)));
	      self#insert (Instru(Pc_assert_exn("Variant non decreasing", id)));
	      self#insert (Instru(Gmp_clear(init_variant)));
	      current_label <- None
	    | Lreal -> assert false (* TODO: reals *)
	    | _ ->
	      current_label <- Some (BegStmt stmt.sid);
	      let term' = self#ctype_fragment (self#term term) in
	      self#insert (If_cond(Cmp(Rlt, term', Zero)));
	      self#insert (Instru(Pc_assert_exn("Variant non positive", id)));
	      current_label <- Some (EndStmt stmt.sid);
	      current_label <- Some (BegIter stmt.sid);
	      let term' = self#ctype_fragment (self#term term) in
	      let variant = self#fresh_ctype_var Cil.intType in
	      self#insert (Decl_ctype_var variant);
	      self#insert (Instru(Affect(variant, term')));
	      current_label <- Some (EndIter stmt.sid);
	      let term' = self#ctype_fragment (self#term term) in
	      self#insert (If_cond(Cmp(Rlt, variant, Zero)));
	      self#insert (Instru(Pc_assert_exn("Variant non positive", id)));
	      self#insert (If_cond(Cmp(Rge, term', variant)));
	      self#insert (Instru(Pc_assert_exn("Variant non decreasing", id)));
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
	self#insert Block_open;
	let str = Format.sprintf "@@FC:REACHABLE_STMT:%i" stmt.sid in
	self#insert (Instru(Pc_to_framac str));
	current_label <- Some (EndStmt stmt.sid);
	self#insert Block_close;
	current_label <- None
      end;
    let kf = Kernel_function.find_englobing_kf stmt in
    begin
      match stmt.skind with
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

  method private predicate_named pnamed : ctype_expr =
    self#predicate pnamed.content

  method private quantif_predicate ~forall logic_vars hyps goal : ctype_expr =
    if (List.length logic_vars) > 1 then
      failwith "quantification on many variables unsupported!";
    let var = self#fresh_ctype_var Cil.intType in
    let guards, vars = Sd_utils.compute_guards [] logic_vars hyps in
    if vars <> [] then
      failwith "Unguarded variables in quantification!";
    let t1,r1,lv,r2,t2 = List.hd guards in
    let iter_name = lv.lv_name in
    self#insert (Decl_ctype_var var);
    self#insert (Instru(Affect(var, (if forall then One else Zero))));
    self#insert Block_open;
    begin
      match t1.term_type with
      | Linteger ->
	begin
	  match t2.term_type with
	  | Linteger ->
	    let fresh_iter = My_gmp_var iter_name in
	    let decl_iter = self#decl_gmp_var fresh_iter in
	    let t1' = self#gmp_fragment (self#term t1) in
	    let t2' = self#gmp_fragment (self#term t2) in
	    let init_iter = self#init_set_gmp_var decl_iter t1' in
	    if r1 = Rlt then
	      self#insert (Instru(Gmp_binop_ui(PlusA,init_iter,init_iter,One)));
	    let exp1 = Gmp_cmpr(r2, init_iter, t2') in
	    let exp2 = if forall then var else Unop(LNot, var) in
	    self#insert (For(None, Some(Binop(LAnd, exp1, exp2)), None));
	    self#insert Block_open;
	    let goal_var = self#predicate_named goal in
	    self#insert (Instru(Affect(var, goal_var)));
	    self#insert (Instru(Gmp_binop_ui(PlusA, init_iter, init_iter,One)));
	    self#insert Block_close;
	    self#insert (Instru(Gmp_clear init_iter));
	    self#insert (Instru(Gmp_clear t1'));
	    self#insert (Instru(Gmp_clear t2'))
	  | Lreal -> assert false (* TODO: reals *)
	  | _ ->
	    let fresh_iter = My_gmp_var iter_name in
	    let decl_iter = self#decl_gmp_var fresh_iter in
	    let t1' = self#gmp_fragment (self#term t1) in
	    let t2' = self#ctype_fragment (self#term t2) in
	    let init_iter = self#init_set_gmp_var decl_iter t1' in
	    if r1 = Rlt then
	      self#insert (Instru(Gmp_binop_ui(PlusA,init_iter,init_iter,One)));
	    let exp1 = Gmp_cmpr_si(r2, init_iter, t2') in
	    let exp2 = if forall then var else Unop(LNot, var) in
	    self#insert (For(None, Some(Binop(LAnd, exp1, exp2)), None));
	    self#insert Block_open;
	    let goal_var = self#predicate_named goal in 
	    self#insert (Instru(Affect(var, goal_var)));
	    self#insert (Instru(Gmp_binop_ui(PlusA, init_iter, init_iter,One)));
	    self#insert Block_close;
	    self#insert (Instru(Gmp_clear init_iter));
	    self#insert (Instru(Gmp_clear t1'))
	end
      | Lreal -> assert false (* TODO: reals *)
      | _ ->
	let iter = My_ctype_var (Cil.intType, iter_name) in
	self#insert (Decl_ctype_var iter);
	let t1' = self#ctype_fragment (self#term t1) in
	let t2' = self#ctype_fragment (self#term t2) in
	let exp1 = Affect(iter, (match r1 with
	  | Rlt -> Binop(PlusA,t1',One)
	  | Rle -> t1'
	  | _ -> assert false))
	in
	let exp2 = Binop(LAnd, (Cmp(r2,iter,t2')),
			 (if forall then var else Unop(LNot, var))) in
	let exp3 = Affect(iter,Binop(PlusA,iter,One)) in
	self#insert (For(Some exp1, Some exp2, Some exp3));
	self#insert Block_open;
	let goal_var = self#predicate_named goal in 
	self#insert (Instru(Affect(var, goal_var)));
	self#insert Block_close
    end;
    self#insert Block_close;
    var
  (* end of quantif_predicate *)

  method private predicate pred : ctype_expr =
    match pred with
    | Ptrue -> One
    | Pfalse -> Zero
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
	  let x' = self#ctype_fragment (self#term pointer) in
	  let y' = self#gmp_fragment (self#term offset) in
	  let var = self#fresh_ctype_var Cil.intType in
	  self#insert (Decl_ctype_var var);
	  let exp1 = Gmp_cmp_ui(Ge, y', Zero) in
	  let exp2 = Gmp_cmp_ui(Lt, y', Pc_dim(x')) in
	  self#insert (Instru(Affect(var, Binop(LAnd, exp1, exp2))));
	  self#insert (Instru(Gmp_clear y'));
	  var
	| Lreal -> assert false (* unreachable *)
	| Ctype (TInt _) ->
	  let x' = self#ctype_fragment (self#term pointer) in
	  let y' = self#ctype_fragment (self#term offset) in
	  let exp1 = Cmp(Rge, y', Zero) in
	  let exp2 = Cmp(Rgt, Pc_dim(x'), y') in
	  Binop(LAnd, exp1, exp2)
	| _ -> assert false (* unreachable *)
      end
    | Pforall(logic_vars,{content=Pimplies(hyps,goal)}) ->
      self#quantif_predicate ~forall:true logic_vars hyps goal
    | Pexists(logic_vars,{content=Pand(hyps,goal)}) ->
      self#quantif_predicate ~forall:false logic_vars hyps goal
    | Pforall _ -> failwith "\\forall not of the form \\forall ...; a ==> b;"
    | Pexists _ -> failwith "\\exists not of the form \\exists ...; a && b;"
    | Pnot(pred1) ->
      let pred1_var = self#predicate_named pred1 in
      Unop(LNot, pred1_var)
    | Pand(pred1,pred2) ->
      let var = self#fresh_ctype_var Cil.intType in
      let pred1_var = self#predicate_named pred1 in
      self#insert (Decl_ctype_var var);
      self#insert (Instru(Affect(var, pred1_var)));
      self#insert (If_cond var);
      self#insert Block_open;
      let pred2_var = self#predicate_named pred2 in
      self#insert (Instru(Affect(var, pred2_var)));
      self#insert Block_close;
      var
    | Por(pred1,pred2) ->
      let var = self#fresh_ctype_var Cil.intType  in
      let pred1_var = self#predicate_named pred1 in
      self#insert (Decl_ctype_var var);
      self#insert (Instru(Affect(var, pred1_var)));
      self#insert (If_cond (Unop(LNot,var)));
      self#insert Block_open;
      let pred2_var = self#predicate_named pred2 in
      self#insert (Instru(Affect(var, pred2_var)));
      self#insert Block_close;
      var
    | Pimplies(pred1,pred2) ->
      let var = self#fresh_ctype_var Cil.intType in
      self#insert (Decl_ctype_var var);
      self#insert (Instru(Affect(var, One)));
      let pred1_var = self#predicate_named pred1 in
      self#insert (If_cond pred1_var);
      self#insert Block_open;
      let pred2_var = self#predicate_named pred2 in
      self#insert (Instru(Affect(var, pred2_var)));
      self#insert Block_close;
      var
    | Piff(pred1,pred2) ->
      let pred1_var = self#predicate_named pred1 in
      let pred2_var = self#predicate_named pred2 in
      let exp1 = Binop(LOr, Unop(LNot, pred1_var), pred2_var) in
      let exp2 = Binop(LOr, Unop(LNot, pred2_var), pred1_var) in
      Binop(LAnd, exp1, exp2)
    | Pif (t,pred1,pred2) -> (* untested *)
      begin
	let term_var = self#term t in
	let res_var = self#fresh_ctype_var Cil.intType in
	self#insert (Decl_ctype_var res_var);
	let f () =
	  let term_var = self#ctype_fragment term_var in
	  self#insert (If_cond term_var);
	  self#insert Block_open;
	  let pred1_var = self#predicate_named pred1 in
	  self#insert (Instru(Affect(res_var, pred1_var)));
	  self#insert Block_close;
	  self#insert Else_cond;
	  self#insert Block_open;
	  let pred2_var = self#predicate_named pred2 in
	  self#insert (Instru(Affect(res_var, pred2_var)));
	  self#insert Block_close;
	  res_var
	in
	match t.term_type with
	| Linteger ->
	  let term_var = self#gmp_fragment term_var in
	  self#insert (If_cond(Gmp_cmp_si(Ne, term_var, Zero)));
	  self#insert Block_open;
	  let pred1_var = self#predicate_named pred1 in
	  self#insert (Instru(Affect(res_var, pred1_var)));
	  self#insert Block_close;
	  self#insert Else_cond;
	  self#insert Block_open;
	  let pred2_var = self#predicate_named pred2 in
	  self#insert (Instru(Affect(res_var, pred2_var)));
	  self#insert Block_close;
	  self#insert (Instru(Gmp_clear term_var));
	  res_var
	| Lreal -> assert false (* unreachable *)
	| Ctype (TInt _) -> f ()
	| Ltype (lt,_) when lt.lt_name = Utf8_logic.boolean -> f ()
	| _ -> assert false (* unreachable *)
      end

    | Prel(rel,t1,t2) ->
      begin
	match t1.term_type, t2.term_type with
	| Linteger, Linteger ->
	  let var = self#fresh_ctype_var Cil.intType in
	  let t1' = self#gmp_fragment (self#term t1) in
	  let t2' = self#gmp_fragment (self#term t2) in
	  self#insert (Decl_ctype_var var);
	  self#insert (Instru(Affect(var, Gmp_cmpr(rel, t1', t2'))));
	  self#insert (Instru(Gmp_clear t1'));
	  self#insert (Instru(Gmp_clear t2'));
	  var
	| Linteger, Ctype (TInt((IULongLong|IULong|IUShort|IUInt|IUChar),_)) ->
	  let var = self#fresh_ctype_var Cil.intType in
	  let t1' = self#gmp_fragment (self#term t1) in
	  let t2' = self#ctype_fragment (self#term t2) in
	  self#insert (Decl_ctype_var var);
	  self#insert (Instru(Affect(var, Gmp_cmpr_ui(rel, t1', t2'))));
	  self#insert (Instru(Gmp_clear t1'));
	  var
	| Linteger, Ctype (TInt _) ->
	  let var = self#fresh_ctype_var Cil.intType in
	  let t1' = self#gmp_fragment (self#term t1) in
	  let t2' = self#ctype_fragment (self#term t2) in
	  self#insert (Decl_ctype_var var);
	  self#insert (Instru(Affect(var, Gmp_cmpr_si(rel, t1', t2'))));
	  self#insert (Instru(Gmp_clear t1'));
	  var
	| Lreal, Lreal -> assert false (* TODO: reals *)
	| Ctype (TInt((IULongLong|IULong|IUShort|IUInt|IUChar),_)), Linteger ->
	  let var = self#fresh_ctype_var Cil.intType in
	  let t1' = self#ctype_fragment (self#term t1) in
	  let t2' = self#gmp_fragment (self#term t2) in
	  let fresh_var' = self#fresh_gmp_var() in
	  let decl_var' = self#decl_gmp_var fresh_var' in
	  let init_var' = self#init_set_ui_gmp_var decl_var' t1' in
	  self#insert (Decl_ctype_var var);
	  self#insert (Instru(Affect(var, Gmp_cmpr(rel, init_var', t2'))));
	  self#insert (Instru(Gmp_clear t2'));
	  self#insert (Instru(Gmp_clear init_var'));
	  var
	| Ctype (TInt _), Linteger ->
	  let var = self#fresh_ctype_var Cil.intType in
	  let t1' = self#ctype_fragment (self#term t1) in
	  let t2' = self#gmp_fragment (self#term t2) in
	  let fresh_var' = self#fresh_gmp_var() in
	  let decl_var' = self#decl_gmp_var fresh_var' in
	  let init_var' = self#init_set_si_gmp_var decl_var' t1' in
	  self#insert (Decl_ctype_var var);
	  self#insert (Instru(Affect(var, Gmp_cmpr(rel, init_var', t2'))));
	  self#insert (Instru(Gmp_clear t2'));
	  self#insert (Instru(Gmp_clear init_var'));
	  var
	| _ ->
          let t1' = self#ctype_fragment (self#term t1) in
          let t2' = self#ctype_fragment (self#term t2) in
	  Cmp(rel, t1', t2')
      end
      
    | Pat(p, LogicLabel(_,stringlabel)) when stringlabel = "Here" ->
      self#predicate_named p
    | Pat (p,_) ->
      Sd_options.Self.warning "%a unsupported!" Printer.pp_predicate pred;
      self#predicate_named p
    | _ ->
      Sd_options.Self.warning "%a unsupported" Printer.pp_predicate pred;
      One
(* end predicate *)
end

class print_insertions insertions ~print_label () = object(self)
  inherit Printer.extensible_printer () as super

  val mutable current_function = None

  method private pp_fresh_gmp fmt = function
  | Fresh_gmp_var id -> Format.fprintf fmt "__stady_gmp_%i" id
  | My_gmp_var name -> Format.fprintf fmt "%s" name

  method private pp_decl_gmp fmt = function
  | Declared_gmp_var v -> self#pp_fresh_gmp fmt v

  method private pp_init_gmp fmt = function
  | Initialized_gmp_var v -> self#pp_decl_gmp fmt v

  method private pp_gexpr fmt =
    self#pp_init_gmp fmt

  method private pp_cexpr fmt = function
  | Fresh_ctype_var (id, _ty) -> Format.fprintf fmt "__stady_term_%i" id
  | My_ctype_var (_, name) -> Format.fprintf fmt "%s" name
  | Zero -> Format.fprintf fmt "0"
  | One -> Format.fprintf fmt "1"
  | Cst s -> Format.fprintf fmt "%s" s
  | Cmp (rel, e1, e2) ->
    Format.fprintf fmt "%a %a %a"
      self#pp_cexpr e1 self#relation rel self#pp_cexpr e2
  | Gmp_cmp (op, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp(%a, %a) %a 0"
      self#pp_gexpr g1 self#pp_gexpr g2 self#binop op
  | Gmp_cmp_ui (op, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp_ui(%a, %a) %a 0"
      self#pp_gexpr g1 self#pp_cexpr g2 self#binop op
  | Gmp_cmp_si (op, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp_si(%a, %a) %a 0"
      self#pp_gexpr g1 self#pp_cexpr g2 self#binop op
  | Gmp_cmpr (rel, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp(%a, %a) %a 0"
      self#pp_gexpr g1 self#pp_gexpr g2 self#relation rel
  | Gmp_cmpr_ui (rel, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp_ui(%a, %a) %a 0"
      self#pp_gexpr g1 self#pp_cexpr g2 self#relation rel
  | Gmp_cmpr_si (rel, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp_si(%a, %a) %a 0"
      self#pp_gexpr g1 self#pp_cexpr g2 self#relation rel
  | Gmp_get_ui g -> Format.fprintf fmt "__gmpz_get_ui(%a)" self#pp_gexpr g
  | Gmp_get_si g -> Format.fprintf fmt "__gmpz_get_si(%a)" self#pp_gexpr g
  | Unop (op, e) -> Format.fprintf fmt "(%a %a)" self#unop op self#pp_cexpr e
  | Binop (op,x,y) ->
    Format.fprintf fmt "(%a %a %a)"
      self#pp_cexpr x self#binop op self#pp_cexpr y
  | Pc_dim e -> Format.fprintf fmt "pathcrawler_dimension(%a)" self#pp_cexpr e
  | Malloc e -> Format.fprintf fmt "malloc(%a)" self#pp_cexpr e
  | Cast (t, e) -> Format.fprintf fmt "(%a)%a" (self#typ None) t self#pp_cexpr e
  | Sizeof t -> Format.fprintf fmt "sizeof(%a)" (self#typ None) t
  | Deref e -> Format.fprintf fmt "*%a" self#pp_cexpr e
  | Index (e, i) -> Format.fprintf fmt "%a[%a]" self#pp_cexpr e self#pp_cexpr i
  | Field (e, s) -> Format.fprintf fmt "%a.%s" self#pp_cexpr e s

  method private pp_garith fmt = function
  | PlusA -> Format.fprintf fmt "add"
  | MinusA -> Format.fprintf fmt "sub"
  | Mult -> Format.fprintf fmt "mul"
  | Div -> Format.fprintf fmt "tdiv_q"
  | Mod -> Format.fprintf fmt "tdiv_r"
  | _ -> assert false (* not used by the translation *)

  method private pp_instruction fmt = function
  | Affect (x,y) -> Format.fprintf fmt "%a = %a" self#pp_cexpr x self#pp_cexpr y
  | Free e -> Format.fprintf fmt "free(%a)" self#pp_cexpr e
  | Pc_to_framac s -> Format.fprintf fmt "pathcrawler_to_framac(\"%s\")" s
  | Pc_assert_exn (s,i) ->
    Format.fprintf fmt "pathcrawler_assert_exception(\"%s\", %i)" s i
  | Ret e -> Format.fprintf fmt "return %a" self#pp_cexpr e
  | Gmp_clear g -> Format.fprintf fmt "__gmpz_clear(%a)" self#pp_gexpr g
  | Gmp_init g -> Format.fprintf fmt "__gmpz_init(%a)" self#pp_decl_gmp g
  | Gmp_init_set (g,g') ->
    Format.fprintf fmt "__gmpz_init_set(%a,%a)"
      self#pp_decl_gmp g self#pp_gexpr g'
  | Gmp_init_set_ui (g,c) ->
    Format.fprintf fmt "__gmpz_init_set_ui(%a,%a)"
      self#pp_decl_gmp g self#pp_cexpr c
  | Gmp_init_set_si (g,c) ->
    Format.fprintf fmt "__gmpz_init_set_si(%a,%a)"
      self#pp_decl_gmp g self#pp_cexpr c
  | Gmp_init_set_str (g,s) ->
    Format.fprintf fmt "__gmpz_init_set_str(%a,\"%s\",10)" self#pp_decl_gmp g s
  | Gmp_set (g,g') ->
    Format.fprintf fmt "__gmpz_set(%a,%a)" self#pp_gexpr g self#pp_gexpr g'
  | Gmp_abs (g,g') ->
    Format.fprintf fmt "__gmpz_abs(%a,%a)" self#pp_gexpr g self#pp_gexpr g'
  | Gmp_ui_sub (r,a,b) ->
    Format.fprintf fmt "__gmpz_ui_sub(%a,%a,%a)"
      self#pp_gexpr r self#pp_cexpr a self#pp_gexpr b
  | Gmp_binop (op,r,a,b) ->
    Format.fprintf fmt "__gmpz_%a(%a,%a,%a)"
      self#pp_garith op self#pp_gexpr r self#pp_gexpr a self#pp_gexpr b
  | Gmp_binop_ui (op,r,a,b) ->
    Format.fprintf fmt "__gmpz_%a_ui(%a,%a,%a)"
      self#pp_garith op self#pp_gexpr r self#pp_gexpr a self#pp_cexpr b
  | Gmp_binop_si (op,r,a,b) ->
    Format.fprintf fmt "__gmpz_%a_si(%a,%a,%a)"
      self#pp_garith op self#pp_gexpr r self#pp_gexpr a self#pp_cexpr b

  method private pp_insertion fmt = function
  | Instru i -> Format.fprintf fmt "%a;@\n" self#pp_instruction i
  | Decl_gmp_var v -> Format.fprintf fmt "mpz_t %a;@\n" self#pp_fresh_gmp v
  | Decl_ctype_var ((Fresh_ctype_var (_id, ty)) as v) ->
    Format.fprintf fmt "%a %a;@\n" (self#typ None) ty self#pp_cexpr v
  | Decl_ctype_var (My_ctype_var (ty, name)) ->
    Format.fprintf fmt "%a %s;@\n" (self#typ None) ty name
  | Decl_ctype_var _ -> assert false
  | If_cond exp -> Format.fprintf fmt "if(%a)@ " self#pp_cexpr exp
  | Else_cond -> Format.fprintf fmt "else@ "
  | For(None, Some e, None) -> Format.fprintf fmt "while(%a)@ " self#pp_cexpr e
  | For(Some i1, Some e, Some i2) ->
    Format.fprintf fmt "for(%a; %a; %a)@ " self#pp_instruction i1
      self#pp_cexpr e self#pp_instruction i2
  | For _ -> assert false (* not used by the translation *)
  | Block_open -> Format.fprintf fmt "{@\n"
  | Block_close -> Format.fprintf fmt "}@\n"

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
	Format.fprintf fmt "%a@ {@\n@[<v 2>@["
	  (self#typ (Some (fun fmt -> Format.fprintf fmt "%s" precond)))
	  (TFun(Cil.intType,x,y,z));
	begin
	  try
	    let q = Hashtbl.find insertions (BegFunc precond) in
	    Queue.iter
	      (fun s ->
		if print_label then
		  Format.fprintf fmt "/* BegFunc %s */ " precond;
		Format.fprintf fmt "%a" self#pp_insertion s) q
	  with _ -> ()
	end;
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
    begin
      try
	let q = Hashtbl.find insertions (BegFunc f.svar.vname) in
	Queue.iter
	  (fun s ->
	    if print_label then
	      Format.fprintf fmt "/* BegFunc %s */ " f.svar.vname;
	    Format.fprintf fmt "%a" self#pp_insertion s) q
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
    let has_code_annots = List.length (Annotations.code_annot stmt) > 0 in
    let kf = Kernel_function.find_englobing_kf stmt in
    let loc = Cil_datatype.Stmt.loc stmt in
    if has_code_annots then Format.fprintf fmt "%a@[<v 2>{@\n"
      (fun fmt -> self#line_directive ~forcefile:false fmt) loc;
    begin
      try
	let q = Hashtbl.find insertions (BegStmt stmt.sid) in
	Queue.iter
	  (fun s ->
	    if print_label then
	      Format.fprintf fmt "/* BegStmt %i */ " stmt.sid;
	    Format.fprintf fmt "%a" self#pp_insertion s) q
      with _ -> ()
    end;
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
		Format.fprintf fmt "%a" self#pp_insertion s) q
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
		Format.fprintf fmt "%a" self#pp_insertion s) q
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
		Format.fprintf fmt "%a" self#pp_insertion s) q
	  with _ -> ()
	end;
	self#stmtkind next fmt stmt.skind
      | _ -> self#stmtkind next fmt stmt.skind
    end;
    begin
      try
	let q = Hashtbl.find insertions (EndStmt stmt.sid) in
	Queue.iter
	  (fun s ->
	    if print_label then
	      Format.fprintf fmt "/* EndStmt %i */ " stmt.sid;
	    Format.fprintf fmt "%a" self#pp_insertion s) q
      with _ -> ()
    end;
    if has_code_annots then Format.fprintf fmt "}@\n @]";
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
