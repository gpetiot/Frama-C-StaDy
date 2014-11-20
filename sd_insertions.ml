
open Cil_types


type label =
| BegStmt of int
| EndStmt of int
| BegFunc of string
| EndFunc of string
| BegIter of int
| EndIter of int
| Glob

type instruction =
| Skip
| Pc_to_framac of string
| Pc_exn of string * int
| IAffect of lval * exp
| IFree of exp
| IRet of exp
| IPc_dim of lval * exp
| IPc_assume of exp
| IMalloc of lval * exp
| IZ_clear of exp
| IZ_init of varinfo
| IZ_init_set of varinfo * exp
| IZ_init_set_ui of varinfo * exp
| IZ_init_set_si of varinfo * exp
| IZ_init_set_str of varinfo * exp
| IZ_set of varinfo * exp
| IZ_abs of varinfo * exp
| IZ_ui_sub of varinfo * exp * exp
| IZ_binop of binop * varinfo * exp * exp
| IZ_binop_ui of binop * varinfo * exp  * exp
| IZ_binop_si of binop * varinfo * exp * exp
| IZ_get_ui of varinfo * exp
| IZ_get_si of varinfo * exp
| IZ_cmp of varinfo * exp * exp
| IZ_cmp_ui of varinfo * exp * exp
| IZ_cmp_si of varinfo * exp * exp

type insertion =
| Instru of instruction
| Decl of varinfo
| Block of insertion list
| IIf of exp * insertion list * insertion list
| IFor of instruction * exp * instruction * insertion list

let binop_to_relation = function
  | Lt -> Rlt
  | Gt -> Rgt
  | Le -> Rle
  | Ge -> Rge
  | Eq -> Req
  | Ne -> Rneq
  | _ -> assert false

let relation_to_binop = function
  | Rlt -> Lt
  | Rgt -> Gt
  | Rle -> Le
  | Rge -> Ge
  | Req -> Eq
  | Rneq -> Ne

module Ins = struct

  let loc = Cil_datatype.Location.unknown

  (* varinfos *)
  let my_varinfo ty varname = Cil.makeVarinfo false false varname ty
  let my_Z_varinfo s = my_varinfo (Sd_utils.mpz_t()) s
  let my_pred_varinfo s = my_varinfo Cil.intType s

  (* expressions *)
  let zero = Cil.zero ~loc
  let one = Cil.one ~loc
  let cmp rel e1 e2 = Cil.mkBinOp ~loc (relation_to_binop rel) e1 e2

  (* instructions *)
  let instru_affect a b = IAffect(a,b)
  let instru_free a = IFree a
  let instru_ret a = IRet a
  let instru_pc_dim a b = IPc_dim(a,b)
  let instru_malloc a b = IMalloc(a,b)
  let instru_Z_clear a = IZ_clear a
  let instru_Z_init a = IZ_init a
  let instru_Z_init_set a b = IZ_init_set(a,b)
  let instru_Z_init_set_ui a b = IZ_init_set_ui(a,b)
  let instru_Z_init_set_si a b = IZ_init_set_si(a,b)
  let instru_Z_init_set_str a b = IZ_init_set_str(a,b)
  let instru_Z_set a b = IZ_set(a,b)
  let instru_Z_abs a b = IZ_abs(a,b)
  let instru_Z_ui_sub a b c = IZ_ui_sub(a,b,c)
  let instru_Z_binop a b c d = IZ_binop(a,b,c,d)
  let instru_Z_binop_ui a b c d = IZ_binop_ui(a,b,c,d)
  let instru_Z_binop_si a b c d = IZ_binop_si(a,b,c,d)
  let instru_Z_get_ui a b = IZ_get_ui(a,b)
  let instru_Z_get_si a b = IZ_get_si(a,b)
  let instru_Z_cmp a b c = IZ_cmp(a,b,c)
  let instru_Z_cmp_ui a b c = IZ_cmp_ui(a,b,c)
  let instru_Z_cmp_si a b c = IZ_cmp_si(a,b,c)

  (* insertions *)
  let decl_varinfo v = Decl v
  let ins_if  a b c = IIf(a,b,c)
  let ins_for a b c d = IFor(a,b,c,d)
end

class gather_insertions props = object(self)
  inherit Visitor.frama_c_inplace as super

  val insertions : (label, insertion Queue.t) Hashtbl.t = Hashtbl.create 64
  val mutable result_varinfo = None
  val mutable in_old_term = false
  val mutable in_old_ptr = false
  val mutable bhv_to_reach_cpt = 0
  val mutable visited_globals = []
  val mutable last_Z_var_id = -1
  val mutable last_ctype_var_id = -1
  val mutable last_pred_var_id = -1

  (* list of stmt ids (sids) used for testing reachibility of some stmts *)
  val mutable stmts_to_reach = []

  (* we can only modify the property_status of the properties that have really
     been translated into pathcrawler_assert_exception *)
  val mutable translated_properties = []

  method get_insertions () = insertions

  method private insert label str =
    try
      Queue.add str (Hashtbl.find insertions label)
    with Not_found ->
      let q = Queue.create() in
      Queue.add str q;
      Hashtbl.add insertions label q

  method private fresh_Z_varinfo() =
    last_Z_var_id <- last_Z_var_id + 1;
    let varname = "__stady_gmp_" ^ (string_of_int last_Z_var_id) in
    Ins.my_Z_varinfo varname

  method private fresh_ctype_varinfo ty =
    last_ctype_var_id <- last_ctype_var_id + 1;
    let varname = "__stady_term_" ^ (string_of_int last_ctype_var_id) in
    Ins.my_varinfo ty varname

  method private fresh_pred_varinfo() =
    last_pred_var_id <- last_pred_var_id + 1;
    let varname = "__stady_pred_" ^ (string_of_int last_pred_var_id) in
    Ins.my_pred_varinfo varname

  method translated_properties() = Sd_utils.no_repeat translated_properties

  method private translate_constant ty = function
    | Integer (i, str_opt) ->
      begin
	match ty with
	| Linteger ->
	  let fresh_var = self#fresh_Z_varinfo() in
	  let insert_0 = Ins.decl_varinfo fresh_var in
	  let str = try Extlib.the str_opt with _ -> Integer.to_string i in
	  let str = Cil.mkString ~loc:Ins.loc str in
	  let insert_1 = Instru(Ins.instru_Z_init_set_str fresh_var str) in
	  [insert_0; insert_1], Cil.evar fresh_var
	| Ctype (TInt(ikind,_)) ->
	  [], Cil.new_exp ~loc:Ins.loc (Const(CInt64(i,ikind,str_opt)))
	| _ -> assert false (* unreachable *)
      end
    | LStr str -> [], Cil.new_exp ~loc:Ins.loc (Const(CStr str))
    | LWStr i64_l -> [], Cil.new_exp ~loc:Ins.loc (Const(CWStr i64_l))
    | LChr c -> [], Cil.new_exp ~loc:Ins.loc (Const(CChr c))
    | LReal {r_literal=s; r_nearest=f; r_lower=l; r_upper=u} ->
      if l <> u then
	Sd_options.Self.warning ~current:true ~once:true
	  "approximating a real number by a float";
      [], Cil.new_exp ~loc:Ins.loc (Const(CReal(f, FLongDouble, Some s)))
    | LEnum e -> [], Cil.new_exp ~loc:Ins.loc (Const(CEnum e))

  method private translate_var lv =
    let varname =
      match self#current_func with
      | Some _ when in_old_term ->
	let prefix =
	  match lv.lv_type with
	  | Ctype ty
	      when (Cil.isPointerType ty || Cil.isArrayType ty) && in_old_ptr ->
	    "old_ptr"
	  | _ -> "old"
	in
	begin
	  match lv.lv_origin with
	  | Some _ -> prefix ^ "_" ^ lv.lv_name
	  | None -> lv.lv_name
	end
      | _ -> lv.lv_name
    in
    match lv.lv_type with
    | Linteger -> Ins.my_Z_varinfo varname
    | Lreal -> assert false (* TODO: reals *)
    | Ctype ty -> Ins.my_varinfo ty varname
    | _ -> assert false

  method private translate_unop op t =
    match t.term_type with
    | Linteger ->
      assert(op = Neg);
      let i_0, e = self#translate_term t in
      let ret = self#fresh_Z_varinfo() in
      let i_1 = Ins.decl_varinfo ret in
      let i_2 = Instru(Ins.instru_Z_init ret) in
      let i_3 = Instru(Ins.instru_Z_ui_sub ret Ins.zero e) in
      let i_4 = Instru(Ins.instru_Z_clear e) in
      i_0 @ [i_1; i_2; i_3; i_4], Lval(Cil.var ret)
    | Lreal -> assert false (* TODO: reals *)
    | _ -> let ins, e = self#translate_term t in ins, UnOp(op,e,(Cil.typeOf e))

  method private translate_binop ty op a b =
    if op = IndexPI || op = PlusPI || op = MinusPI then
      let i_0, a' = self#translate_term a in
      let i_1, b' = self#translate_term b in
      let i_2, e =
	match b.term_type with
	| Linteger ->
	  let v = self#fresh_ctype_varinfo Cil.intType in
	  let ii_0 = Ins.decl_varinfo v in
	  let ii_1 = Instru(Ins.instru_Z_get_si v b') in
	  let ii_2 = Instru(Ins.instru_Z_clear b') in
	  [ii_0; ii_1; ii_2], Cil.evar v
	| _ -> [], b'
      in
      let e' = Cil.new_exp ~loc:Ins.loc (BinOp(op,a',e,(Cil.typeOf a'))) in
      i_0 @ i_1 @ i_2, e'.enode
    else
      let inserts_0, x = self#translate_term a in
      let inserts_1, y = self#translate_term b in
      begin
	match ty with
	| Linteger ->
	  let fresh_var = self#fresh_Z_varinfo() in
	  let insert_2 = Ins.decl_varinfo fresh_var in
	  let insert_3 = Instru(Ins.instru_Z_init fresh_var) in
	  let clear_t1 = match a.term_type with
	    Linteger -> [Instru(Ins.instru_Z_clear x)] | _ -> []
	  in
	  let clear_t2 = match b.term_type with
	    Linteger -> [Instru(Ins.instru_Z_clear y)] | _ -> []
	  in
	  let inserts =
	    match a.term_type, b.term_type with
	    | Linteger, Linteger ->
	      [Instru(Ins.instru_Z_binop op fresh_var x y)]
	    | Linteger, Ctype ty' when Cil.isUnsignedInteger ty' ->
	      [Instru(Ins.instru_Z_binop_ui op fresh_var x y)]
	    | Linteger, Ctype ty' when Cil.isSignedInteger ty' ->
	      [Instru(Ins.instru_Z_binop_si op fresh_var x y)]
	    | Ctype ty', Linteger when Cil.isUnsignedInteger ty' ->
	      if op = PlusA || op = Mult then
	        [Instru(Ins.instru_Z_binop_ui op fresh_var y x)]
	      else
		assert false (* TODO *)
	    | Ctype ty', Linteger when Cil.isSignedInteger ty' ->
	      if op = PlusA || op = Mult then
	        [Instru(Ins.instru_Z_binop_si op fresh_var y x)]
	      else
		assert false (* TODO *)
	    | Ctype(TInt _), Ctype(TInt _) ->
	      let fresh_var1 = self#fresh_Z_varinfo() in
	      let insert_4 = Ins.decl_varinfo fresh_var1 in
	      let fresh_var2 = self#fresh_Z_varinfo() in
	      let insert_5 = Ins.decl_varinfo fresh_var2 in
	      let insert_6 = Instru(Ins.instru_Z_init_set_si fresh_var1 x) in
	      let insert_7 = Instru(Ins.instru_Z_init_set_si fresh_var2 y) in
	      let fresh_var1 = Cil.evar fresh_var1
	      and fresh_var2 = Cil.evar fresh_var2 in
	      [insert_4; insert_5; insert_6; insert_7;
	       Instru(Ins.instru_Z_binop op fresh_var fresh_var1 fresh_var2);
	       Instru(Ins.instru_Z_clear fresh_var1);
	       Instru(Ins.instru_Z_clear fresh_var2)]
	    | _ -> assert false
	  in
	  inserts_0 @ inserts_1 @ [insert_2; insert_3] @ inserts
	  @ clear_t1 @ clear_t2,
	  (Cil.evar fresh_var).enode
	| Lreal -> assert false (* TODO: reals *)
	| Ltype (lt,_) when lt.lt_name = Utf8_logic.boolean ->
	  begin
	    match a.term_type, b.term_type with
	    | Linteger, Linteger ->
	      let var = self#fresh_ctype_varinfo Cil.intType in
	      let insert_2 = Ins.decl_varinfo var in
	      let tmp = self#fresh_ctype_varinfo Cil.intType in
	      let e_tmp = Cil.evar tmp in
	      let i_1 = Ins.decl_varinfo tmp in
	      let i_2 =	Instru(Ins.instru_Z_cmp tmp x y) in
	      let op = binop_to_relation op in
	      let lvar = Cil.var var in
	      let insert_3 =
		Instru(Ins.instru_affect lvar (Ins.cmp op e_tmp Ins.zero)) in
	      let insert_4 = Instru(Ins.instru_Z_clear x) in
	      let insert_5 = Instru(Ins.instru_Z_clear y) in
	      inserts_0 @ inserts_1
	      @ [insert_2; i_1; i_2; insert_3; insert_4; insert_5],
	      (Cil.evar var).enode
	    | _ ->
	      inserts_0 @ inserts_1,
	      (Cil.mkBinOp ~loc:Ins.loc op x y).enode
	  end
	| _ -> assert false (* unreachable ? *)
      end

  method private translate_tif cond then_b else_b =
    match then_b.term_type with
    | Linteger ->
      let fresh_var = self#fresh_Z_varinfo() in
      let insert_0 = Ins.decl_varinfo fresh_var in
      let insert_1 = Instru(Ins.instru_Z_init fresh_var) in
      let inserts_2, cond' = self#translate_term cond in
      let tmp = self#fresh_ctype_varinfo Cil.intType in
      let e_tmp = Cil.evar tmp in
      let i_1 = Ins.decl_varinfo tmp in
      let i_2 = Instru(Ins.instru_Z_cmp_si tmp cond' Ins.zero) in
      let inserts_then_0, then_b' = self#translate_term then_b in
      let inserts_then = inserts_then_0
	@ [Instru(Ins.instru_Z_set fresh_var then_b');
	   Instru(Ins.instru_Z_clear then_b')]
      in
      let inserts_else_0, else_b' = self#translate_term else_b in
      let inserts_else = inserts_else_0
	@ [Instru(Ins.instru_Z_set fresh_var else_b');
	   Instru(Ins.instru_Z_clear else_b')]
      in
      let insert_3 =
	Ins.ins_if (Ins.cmp Rneq e_tmp Ins.zero) inserts_then inserts_else in
      let insert_4 = Instru(Ins.instru_Z_clear cond') in
      [insert_0; insert_1] @ inserts_2 @ [i_1; i_2; insert_3; insert_4],
      (Cil.evar fresh_var).enode
    | Lreal -> assert false (* TODO: reals *)
    | _ -> assert false (* unreachable *)

  method private translate_at t = function
  | LogicLabel(_,stringlabel) ->
    if stringlabel = "Old" || stringlabel = "Pre" then
      let is_ptr = match t.term_node with TLval(TMem _,_) -> true | _-> false in
      if is_ptr then in_old_ptr <- true;
      in_old_term <- true;
      let ins, v = self#translate_term t in
      if is_ptr then in_old_ptr <- false;
      in_old_term <- false;
      ins, v.enode
    else
      (* label Post is only encoutered in post-conditions, and \at(t,Post)
	 in a post-condition is t *)
      if stringlabel = "Post" || stringlabel = "Here" then
	let ins, v = self#translate_term t in
	ins, v.enode
      else
	Sd_options.Self.not_yet_implemented
	  "Sd_insertions.gather_insertions#term_node \\at(%a,%s)"
	  Sd_debug.pp_term t stringlabel
  | _ -> assert false

  (* C type -> logic type *)
  method private translate_logic_coerce lt t = match lt with
  | Linteger ->
    let ty =
      match t.term_type with
      | Ctype x -> Ctype (Cil.unrollType x)
      | x -> x
    in
    let inserts_0, v = self#translate_term t in
    let fresh_var = self#fresh_Z_varinfo() in
    let insert_1 = Ins.decl_varinfo fresh_var in
    let init_set =
      match ty with
      | Ctype x when Cil.isUnsignedInteger x -> Ins.instru_Z_init_set_ui
      | Ctype x when Cil.isSignedInteger x -> Ins.instru_Z_init_set_si
      | _ -> assert false
    in
    let insert_2 = Instru(init_set fresh_var v) in
    inserts_0 @ [insert_1; insert_2], (Cil.evar fresh_var).enode
  | Lreal -> assert false (* TODO: reals *)
  | _ -> assert false (* unreachable *)

  (* logic type -> C type *)
  method private translate_coerce t ty = match t.term_type with
  | Linteger ->
    let inserts_0, v = self#translate_term t in
    let var = self#fresh_ctype_varinfo ty in
    let insert_1 = Ins.decl_varinfo var in
    let insert_2 =
      match ty with
      | x when Cil.isUnsignedInteger x -> Instru(Ins.instru_Z_get_ui var v)
      | x when Cil.isSignedInteger x -> Instru(Ins.instru_Z_get_si var v)
      | _ -> assert false
    in
    let insert_3 = Instru(Ins.instru_Z_clear v) in
    inserts_0 @ [insert_1; insert_2; insert_3], (Cil.evar var).enode
  | Lreal -> assert false (* TODO: reals *)
  | _ -> assert false (* unreachable *)

  method private translate_lambda li lower upper q t =
    assert(lower.term_type = Linteger && upper.term_type = Linteger);
    let name = li.l_var_info.lv_name in
    let init_val =
      if name = "\\sum" || name = "\\numof" then Ins.zero else Ins.one in
    let fresh_var = self#fresh_Z_varinfo() in
    let i_0 = Ins.decl_varinfo fresh_var in
    let i_1 = Instru(Ins.instru_Z_init_set_si fresh_var init_val) in
    let i_3, low = self#translate_term lower in
    let i_4, up = self#translate_term upper in
    let fresh_iter = Ins.my_Z_varinfo q.lv_name in
    let i_5 = Ins.decl_varinfo fresh_iter in
    let i_6 = Instru(Ins.instru_Z_init_set fresh_iter low) in
    let ins_b_0, lambda_t = self#translate_term t in
    let e_fresh_var = Cil.evar fresh_var in
    let ins_b_1, clear_lambda =
      match name with
      | s when s = "\\sum" ->
	Instru(Ins.instru_Z_binop PlusA fresh_var e_fresh_var lambda_t),
	[Instru(Ins.instru_Z_clear lambda_t)]
      | s when s = "\\product" ->
	Instru(Ins.instru_Z_binop Mult fresh_var e_fresh_var lambda_t),
	[Instru(Ins.instru_Z_clear lambda_t)]
      | s when s = "\\numof" ->
	(* lambda_t of type: Ltype(lt,_) when lt.lt_name = Utf8_logic.boolean *)
	let cond = Ins.cmp Rneq lambda_t Ins.zero in
	let instr =
	  Instru(Ins.instru_Z_binop_ui PlusA fresh_var e_fresh_var Ins.one) in
	Ins.ins_if cond [instr] [], []
      | _ -> assert false
    in
    let e_fresh_iter = Cil.evar fresh_iter in
    let ins_b_2 =
      Instru(Ins.instru_Z_binop_ui PlusA fresh_iter e_fresh_iter Ins.one) in
    let tmp = self#fresh_ctype_varinfo Cil.intType in
    let e_tmp = Cil.evar tmp in
    let ii_1 = Ins.decl_varinfo tmp in
    let ii_2 = Instru(Ins.instru_Z_cmp tmp e_fresh_iter up) in
    let ii_3 = Instru(Ins.instru_Z_cmp tmp e_fresh_iter up) in
    let ins_b = ins_b_0 @ [ins_b_1; ins_b_2; ii_3] @ clear_lambda in
    let i_7 = IFor(Skip, Ins.cmp Rle e_tmp Ins.zero, Skip, ins_b) in
    let e_fresh_iter = Cil.evar fresh_iter in
    let i_8 = Instru(Ins.instru_Z_clear e_fresh_iter) in
    let i_9 = Instru(Ins.instru_Z_clear low) in
    let i_10 = Instru(Ins.instru_Z_clear up) in
    let inserts_block =
      i_3 @ i_4 @ [i_5; i_6; ii_1; ii_2; i_7; i_8; i_9; i_10] in
    [i_0; i_1; Block inserts_block], e_fresh_var.enode

  method private translate_app li _ params =
    let s = li.l_var_info.lv_name in
    let ty = Extlib.the li.l_type in
    match ty with
    | Linteger ->
      if s = "\\abs" then
	begin
	  let param = List.hd params in
	  assert (List.tl params = []);
	  let inserts_0, x = self#translate_term param in
	  let fresh_var = self#fresh_Z_varinfo() in
	  let insert_1 = Ins.decl_varinfo fresh_var in
	  let insert_2 = Instru(Ins.instru_Z_init fresh_var) in
	  let insert_3 = Instru(Ins.instru_Z_abs fresh_var x) in
	  let insert_4 = Instru(Ins.instru_Z_clear x) in
	  inserts_0 @ [insert_1; insert_2; insert_3; insert_4],
	  (Cil.evar fresh_var).enode
	end
      else
	if s = "\\sum" || s = "\\product" || s = "\\numof" then
	  match params with
	  | [l;u;{term_node=Tlambda([q],t)}] -> self#translate_lambda li l u q t
	  | _ -> assert false
	else assert false
    | Lreal -> assert false (* TODO: reals *)
    | _ -> assert false (* unreachable *)

  method private translate_cast ty t =
    match t.term_type with (* source type *)
    | Linteger ->
      let inserts_0, e = self#translate_term t in
      let var = self#fresh_ctype_varinfo ty in
      let insert_1 = Ins.decl_varinfo var in
      let get =
  	match ty with (* dest type *)
  	| x when Cil.isUnsignedInteger x -> Ins.instru_Z_get_ui
  	| x when Cil.isSignedInteger x -> Ins.instru_Z_get_si
  	| _ -> assert false (* unreachable *)
      in
      let insert_2 = Instru(get var e) in
      let insert_3 = Instru(Ins.instru_Z_clear e) in
      inserts_0 @ [insert_1; insert_2; insert_3], (Cil.evar var).enode
    | Lreal -> assert false (* reals *)
    | Ctype _ ->
      let ins, e = self#translate_term t in
      ins, CastE (ty, e)
    | _ -> assert false (* unreachable *)

  method private translate_term_node t = match t.term_node with
  | TConst c ->
    let ins, e = self#translate_constant t.term_type c in ins, e.enode
  | TLval tl -> let ins, lv = self#translate_lval tl in ins, Lval lv
  | TSizeOf ty -> [], SizeOf ty
  | TSizeOfE t -> let ins, e = self#translate_term t in ins, SizeOfE e
  | TSizeOfStr str -> [], SizeOfStr str
  | TAlignOf ty -> [], AlignOf ty
  | TAlignOfE t -> let ins, e = self#translate_term t in ins, AlignOfE e
  | TUnOp (op,t) -> self#translate_unop op t
  | TBinOp (op,a,b) -> self#translate_binop t.term_type op a b
  | TCastE (ty,t) -> self#translate_cast ty t
  | TAddrOf tl -> let ins, lv = self#translate_lval tl in ins, AddrOf lv
  | TStartOf tl -> let ins, lv = self#translate_lval tl in ins, StartOf lv
  | Tapp (li,ll,params) -> self#translate_app li ll params
  | Tlambda _ -> assert false
  | TDataCons _ -> assert false
  | Tif (x,y,z) -> self#translate_tif x y z
  | Tat (t,l) -> self#translate_at t l
  | Tbase_addr _ -> assert false
  | Toffset _ -> assert false
  | Tblock_length _ -> assert false
  | Tnull -> [], Ins.zero.enode
  | TLogic_coerce (lt,t) -> self#translate_logic_coerce lt t
  | TCoerce (t,ty) -> self#translate_coerce t ty
  | TCoerceE (t, {term_type=(Linteger|Lreal) as lt}) ->
    self#translate_logic_coerce lt t
  | TCoerceE (t, {term_type=Ctype ty}) -> self#translate_coerce t ty
  | TCoerceE _ -> assert false
  | TUpdate _ -> assert false
  | Ttypeof _ -> assert false
  | Ttype _ -> assert false
  | Tempty_set -> assert false
  | Tunion _ -> assert false
  | Tinter _ -> assert false
  | Tcomprehension _ -> assert false
  | Trange _ -> assert false
  | Tlet _ -> assert false

  method private translate_term t =
    let ins, enode = self#translate_term_node t in
    ins, Cil.new_exp ~loc:Ins.loc enode

  method private translate_lhost = function
  | TVar lv -> [], Var(self#translate_var lv)
  | TResult _ -> [], Var (Extlib.the result_varinfo)
  | TMem t -> let ins, t = self#translate_term t in ins, Mem t

  method private translate_offset = function
  | TNoOffset -> [], NoOffset
  | TField (fi,o) -> let ins, o' = self#translate_offset o in ins, Field(fi,o')
  | TModel _ -> assert false (* TODO *)
  | TIndex(t,o) ->
    let ins, e = self#translate_term t in
    let ins, e =
      match t.term_type with
      | Linteger ->
  	let tmp = self#fresh_ctype_varinfo Cil.intType in
  	let i_1 = Ins.decl_varinfo tmp in
  	let i_2 = Instru(Ins.instru_Z_get_si tmp e) in
	ins @ [i_1; i_2], Cil.evar tmp
      | Lreal -> assert false (* unreachable *)
      | _ -> ins, e
    in
    let ins', o' = self#translate_offset o in
    ins @ ins', Index(e,o')

  method private translate_lval (a,b) =
    let aux() =
      let ins, a' = self#translate_lhost a in
      let ins', b' = self#translate_offset b in
      ins @ ins', (a',b')
    in
    match Cil.typeOfTermLval (a,b) with
    | Linteger ->
      let fresh_var = self#fresh_Z_varinfo() in
      let ins_0, t' = aux() in
      let ins_1 = Ins.decl_varinfo fresh_var in
      let e_t' = Cil.new_exp ~loc:Ins.loc (Lval t') in
      let ins_2 = Instru(Ins.instru_Z_init_set fresh_var e_t') in
      ins_0 @ [ins_1; ins_2], Cil.var fresh_var
    | Lreal -> assert false (* TODO *)
    | _ -> aux()
    

  method private translate_pnamed p = self#translate_predicate p.content

  method private translate_rel rel t1 t2 =
    let inserts_0, t1' = self#translate_term t1 in
    let inserts_1, t2' = self#translate_term t2 in
    let clear_t1 = match t1.term_type with
	Linteger -> [Instru(Ins.instru_Z_clear t1')] | _ -> []
    in
    let clear_t2 = match t2.term_type with
	Linteger -> [Instru(Ins.instru_Z_clear t2')] | _ -> []
    in
    let inserts, ret =
      match t1.term_type, t2.term_type with
      | Linteger, Linteger ->
	let var = self#fresh_ctype_varinfo Cil.intType in
	let insert_2 = Ins.decl_varinfo var in
	let insert_3 = Instru(Ins.instru_Z_cmp var t1' t2') in
	[insert_2; insert_3], Ins.cmp rel (Cil.evar var) Ins.zero
      | Linteger, Ctype x ->
	let var = self#fresh_ctype_varinfo Cil.intType in
	let insert_2 = Ins.decl_varinfo var in
	let cmp =
	  if Cil.isUnsignedInteger x then Ins.instru_Z_cmp_ui
	  else if Cil.isSignedInteger x then Ins.instru_Z_cmp_si
	  else assert false
	in
	let insert_3 = Instru(cmp var t1' t2') in
	[insert_2; insert_3], Ins.cmp rel (Cil.evar var) Ins.zero
      | Lreal, Lreal -> assert false (* TODO: reals *)
      | Ctype x, Linteger ->
	let var = self#fresh_ctype_varinfo Cil.intType in
	let fresh_var' = self#fresh_Z_varinfo() in
	let insert_2 = Ins.decl_varinfo fresh_var' in
	let init_set =
	  if Cil.isUnsignedInteger x then Ins.instru_Z_init_set_ui
	  else if Cil.isSignedInteger x then Ins.instru_Z_init_set_si
	  else assert false
	in
	let insert_3 = Instru(init_set fresh_var' t1') in
	let insert_4 = Ins.decl_varinfo var in
	let e_fresh_var = Cil.evar fresh_var' in
	let insert_5 = Instru(Ins.instru_Z_cmp var e_fresh_var t2') in
	let insert_7 = Instru(Ins.instru_Z_clear e_fresh_var) in
	[insert_2; insert_3; insert_4; insert_5; insert_7],
	Ins.cmp rel (Cil.evar var) Ins.zero
      | _ -> [], Ins.cmp rel t1' t2'
    in
    inserts_0 @ inserts_1 @ inserts @ clear_t1 @ clear_t2, ret

  method private translate_and p q =
    let var = self#fresh_pred_varinfo() in
    let inserts_0, pred1_var = self#translate_pnamed p in
    let insert_1 = Ins.decl_varinfo var in
    let lvar = Cil.var var in
    let insert_2 = Instru(Ins.instru_affect lvar pred1_var) in
    let inserts_b_0, pred2_var = self#translate_pnamed q in
    let insert_b_1 = Instru(Ins.instru_affect lvar pred2_var) in
    let e_var = Cil.evar var in
    let insert_3 = Ins.ins_if e_var (inserts_b_0 @ [insert_b_1]) [] in
    inserts_0 @ [insert_1; insert_2; insert_3], e_var

  method private translate_or p q =
    let var = self#fresh_pred_varinfo()  in
    let inserts_0, pred1_var = self#translate_pnamed p in
    let insert_1 = Ins.decl_varinfo var in
    let lvar = Cil.var var in
    let insert_2 = Instru(Ins.instru_affect lvar pred1_var) in
    let inserts_b_0, pred2_var = self#translate_pnamed q in
    let insert_b_1 = Instru(Ins.instru_affect lvar pred2_var) in
    let e_var = Cil.evar var in
    let insert_3 = Ins.ins_if e_var [] (inserts_b_0 @ [insert_b_1]) in
    inserts_0 @ [insert_1; insert_2; insert_3], e_var

  method private translate_implies p q =
    let var = self#fresh_pred_varinfo() in
    let insert_0 = Ins.decl_varinfo var in
    let lvar = Cil.var var in
    let insert_1 = Instru(Ins.instru_affect lvar Ins.one) in
    let inserts_2, pred1_var = self#translate_pnamed p in
    let inserts_b_0, pred2_var = self#translate_pnamed q in
    let insert_b_1 = Instru(Ins.instru_affect lvar pred2_var) in
    let insert_3 = Ins.ins_if pred1_var (inserts_b_0 @ [insert_b_1]) [] in
    [insert_0; insert_1] @ inserts_2 @ [insert_3], Cil.evar var

  method private translate_equiv p q =
    let inserts_0, pred1_var = self#translate_pnamed p in
    let inserts_1, pred2_var = self#translate_pnamed q in
    let loc = Ins.loc in
    let not_pred1_var = Cil.new_exp ~loc (UnOp(LNot, pred1_var, Cil.intType)) in
    let not_pred2_var = Cil.new_exp ~loc (UnOp(LNot, pred2_var, Cil.intType)) in
    let exp1 = Cil.mkBinOp ~loc LOr not_pred1_var pred2_var in
    let exp2 = Cil.mkBinOp ~loc LOr not_pred2_var pred1_var in
    inserts_0 @ inserts_1, Cil.mkBinOp ~loc LAnd exp1 exp2

  method private translate_not p =
    let ins, p' = self#translate_pnamed p in
    ins, Cil.new_exp ~loc:Ins.loc (UnOp(LNot, p', Cil.intType))

  method private translate_pif t p q =
    let inserts_0, term_var = self#translate_term t in
    let res_var = self#fresh_pred_varinfo() in
    let insert_1 = Ins.decl_varinfo res_var in
    let cond, ii, insert_3 =
      match t.term_type with
      | Linteger ->
	let tmp = self#fresh_ctype_varinfo Cil.intType in
	let i_1 = Ins.decl_varinfo tmp in
	let i_2 = Instru(Ins.instru_Z_cmp_si tmp term_var Ins.zero) in
	Ins.cmp Rneq (Cil.evar tmp) Ins.zero,
	[i_1; i_2],
	[Instru(Ins.instru_Z_clear term_var)]
      | Lreal -> assert false (* unreachable *)
      | Ctype (TInt _) ->
	Ins.cmp Rneq term_var Ins.zero, [], []
      | Ltype (lt,_) when lt.lt_name = Utf8_logic.boolean ->
	Ins.cmp Rneq term_var Ins.zero, [], []
      | _ -> assert false (* unreachable *)
    in
    let inserts_then_0, pred1_var = self#translate_pnamed p in
    let lres_var = Cil.var res_var in
    let insert_then_1 = Instru(Ins.instru_affect lres_var pred1_var) in
    let inserts_then = inserts_then_0 @ [insert_then_1] in
    let inserts_else_0, pred2_var = self#translate_pnamed q in
    let insert_else_1 = Instru(Ins.instru_affect lres_var pred2_var) in
    let inserts_else = inserts_else_0 @ [insert_else_1] in
    let insert_2 = Ins.ins_if cond inserts_then inserts_else in
    inserts_0 @ ii @ [insert_1; insert_2] @ insert_3, Cil.evar res_var

  method private unsupported_predicate p =
    Sd_options.Self.warning ~current:true "%a unsupported"
      Printer.pp_predicate p;
    [], Ins.one

  method private translate_valid term =
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
    let inserts_0, x' = self#translate_term pointer in
    let inserts_1, y' = self#translate_term offset in
    let inserts, ret =
      match offset.term_type with
      | Linteger ->
	let var = self#fresh_pred_varinfo() in
	let insert_2 = Ins.decl_varinfo var in
	let tmp' = self#fresh_ctype_varinfo Cil.intType in
	let ii_1 = Ins.decl_varinfo tmp' in
	let ii_2 = Instru(Ins.instru_Z_cmp_ui tmp' y' Ins.zero) in
	let tmp = self#fresh_ctype_varinfo Cil.intType in
	let i_1 = Ins.decl_varinfo tmp in
	let ltmp = Cil.var tmp in
	let i_2 = Instru(Ins.instru_pc_dim ltmp x') in
	let tmp'' = self#fresh_ctype_varinfo Cil.intType in
	let ii_3 = Ins.decl_varinfo tmp'' in
	let ii_4 = Instru(Ins.instru_Z_cmp_ui tmp'' y' (Cil.evar tmp)) in
	let e1 = Ins.cmp Rge (Cil.evar tmp') Ins.zero in
	let e2 = Ins.cmp Rlt (Cil.evar tmp'') Ins.zero in
	let e3 = Cil.mkBinOp ~loc:Ins.loc LAnd e1 e2 in
	let lvar = Cil.var var in
	let insert_3 = Instru(Ins.instru_affect lvar e3) in
	let insert_4 = Instru(Ins.instru_Z_clear y') in
	[insert_2; ii_1; ii_2; i_1; i_2; ii_3; ii_4; insert_3; insert_4],
	(Cil.evar var)
      | Ctype (TInt _) ->
	let tmp = self#fresh_ctype_varinfo Cil.intType in
	let i_1 = Ins.decl_varinfo tmp in
	let ltmp = Cil.var tmp in
	let i_2 = Instru(Ins.instru_pc_dim ltmp x') in
	let e1 = Ins.cmp Rge y' Ins.zero in
	let e2 = Ins.cmp Rgt (Cil.evar tmp) y' in
	[i_1; i_2], Cil.mkBinOp ~loc:Ins.loc LAnd e1 e2
      | _ -> assert false (* unreachable *)
    in
    inserts_0 @ inserts_1 @ inserts, ret

  method private translate_quantif ~forall logic_vars hyps goal =
    if (List.length logic_vars) > 1 then
      failwith "quantification on many variables unsupported!"; (* TODO *)
    let var = self#fresh_pred_varinfo() in
    let lvar = List.hd logic_vars in
    let t1,r1,r2,t2 = Sd_utils.extract_guards lvar hyps in
    let iter_name = lvar.lv_name in
    let insert_0 = Ins.decl_varinfo var in
    let init_val = if forall then Ins.one else Ins.zero in
    let lvar = Cil.var var in
    let insert_1 = Instru(Ins.instru_affect lvar init_val) in
    let inserts_3 =
      match t1.term_type with
      | Linteger ->
	begin
	  match t2.term_type with
	  | Linteger ->
	    let fresh_iter = Ins.my_Z_varinfo iter_name in
	    let insert_0 = Ins.decl_varinfo fresh_iter in
	    let inserts_1, t1' = self#translate_term t1 in
	    let inserts_2, t2' = self#translate_term t2 in
	    let insert_3 = Instru(Ins.instru_Z_init_set fresh_iter t1') in
	    let e_fresh_iter = Cil.evar fresh_iter in
	    let inserts_4 =
	      if r1=Rlt then
		[Instru(Ins.instru_Z_binop_ui
			  PlusA fresh_iter e_fresh_iter Ins.one)]
	      else []
	    in
	    let tmp = self#fresh_ctype_varinfo Cil.intType in
	    let i_1 = Ins.decl_varinfo tmp in
	    let e_fresh_iter = Cil.evar fresh_iter in
	    let i_2 = Instru(Ins.instru_Z_cmp tmp e_fresh_iter t2') in
	    let e_var = Cil.evar var in
	    let exp2 =
	      if forall then e_var
	      else Cil.new_exp ~loc:Ins.loc (UnOp(LNot,e_var,Cil.intType))
	    in
	    let ins_b_0, goal_var = self#translate_pnamed goal in
	    let ins_b_1 = Instru(Ins.instru_affect lvar goal_var) in
	    let ins_b_2 =
	      Instru
		(Ins.instru_Z_binop_ui PlusA fresh_iter e_fresh_iter Ins.one) in
	    let i_3 = Instru(Ins.instru_Z_cmp tmp e_fresh_iter t2') in
	    let inserts_block = ins_b_0 @ [ins_b_1; ins_b_2; i_3] in
	    let e1 = Ins.cmp r2 (Cil.evar tmp) Ins.zero in
	    let e2 = Cil.mkBinOp ~loc:Ins.loc LAnd e1 exp2 in
	    let insert_5 = Ins.ins_for Skip e2 Skip inserts_block in
	    let insert_6 = Instru(Ins.instru_Z_clear e_fresh_iter) in
	    let insert_7 = Instru(Ins.instru_Z_clear t1') in
	    let insert_8 = Instru(Ins.instru_Z_clear t2') in
	    [insert_0] @ inserts_1 @ inserts_2 @ [insert_3] @ inserts_4
	    @ [i_1; i_2; insert_5; insert_6; insert_7; insert_8]
	  | Lreal -> assert false (* TODO: reals *)
	  | _ ->
	    let fresh_iter = Ins.my_Z_varinfo iter_name in
	    let insert_0 = Ins.decl_varinfo fresh_iter in
	    let inserts_1, t1' = self#translate_term t1 in
	    let inserts_2, t2' = self#translate_term t2 in
	    let insert_3 = Instru(Ins.instru_Z_init_set fresh_iter t1') in
	    let e_fresh_iter = Cil.evar fresh_iter in
	    let inserts_4 =
	      if r1=Rlt then
		[Instru(Ins.instru_Z_binop_ui
			  PlusA fresh_iter e_fresh_iter Ins.one)]
	      else []
	    in
	    let tmp = self#fresh_ctype_varinfo Cil.intType in
	    let i_1 = Ins.decl_varinfo tmp in
	    let i_2 = Instru(Ins.instru_Z_cmp_si tmp e_fresh_iter t2') in
	    let e_var = Cil.evar var in
	    let exp2 =
	      if forall then e_var
	      else Cil.new_exp ~loc:Ins.loc (UnOp(LNot,e_var,Cil.intType))
	    in
	    let ins_b_0, goal_var = self#translate_pnamed goal in 
	    let ins_b_1 = Instru(Ins.instru_affect lvar goal_var) in
	    let ins_b_2 =
	      Instru(Ins.instru_Z_binop_ui
		       PlusA fresh_iter e_fresh_iter Ins.one) in
	    let i_3 = Instru(Ins.instru_Z_cmp_si tmp e_fresh_iter t2') in
	    let inserts_block = ins_b_0 @ [ins_b_1; ins_b_2; i_3] in
	    let e1 = Ins.cmp r2 (Cil.evar tmp) Ins.zero in
	    let e2 = Cil.mkBinOp ~loc:Ins.loc LAnd e1 exp2 in
	    let insert_5 = Ins.ins_for Skip e2 Skip inserts_block in
	    let insert_6 = Instru(Ins.instru_Z_clear e_fresh_iter) in
	    let insert_7 = Instru(Ins.instru_Z_clear t1') in
	    [insert_0] @ inserts_1 @ inserts_2 @ [insert_3] @ inserts_4
	    @ [i_1; i_2; insert_5; insert_6; insert_7]
	end
      | Lreal -> assert false (* TODO: reals *)
      | _ ->
	let iter = Ins.my_varinfo Cil.intType iter_name in
	let insert_0 = Ins.decl_varinfo iter in
	let inserts_1, t1' = self#translate_term t1 in
	let inserts_2, t2' = self#translate_term t2 in
	let liter = Cil.var iter in
	let init = Ins.instru_affect liter (match r1 with
	  | Rlt -> Cil.mkBinOp ~loc:Ins.loc PlusA t1' Ins.one
	  | Rle -> t1'
	  | _ -> assert false)
	in
	let e_var = Cil.evar var in
	let e_iter = Cil.evar iter in
	let e1 = Ins.cmp r2 e_iter t2' in
	let e2 =
	  if forall then e_var
	  else Cil.new_exp ~loc:Ins.loc (UnOp(LNot,e_var,Cil.intType))
	in
	let exp2 = Cil.mkBinOp ~loc:Ins.loc LAnd e1 e2 in
	let e3 = Cil.mkBinOp ~loc:Ins.loc PlusA e_iter Ins.one in
	let next = Ins.instru_affect liter e3 in
	let ins_b_0, goal_var = self#translate_pnamed goal in
	let ins_b_1 = Instru(Ins.instru_affect lvar goal_var) in
	let inserts_block = ins_b_0 @ [ins_b_1]	in
	let insert_3 = Ins.ins_for init exp2 next inserts_block in
	[insert_0] @ inserts_1 @ inserts_2 @ [insert_3]
    in
    let insert_4 = Block inserts_3 in
    [insert_0; insert_1; insert_4], Cil.evar var

  method private translate_predicate = function
  | Pfalse -> [], Ins.zero
  | Ptrue -> [], Ins.one
  | Papp _ as p -> self#unsupported_predicate p
  | Pseparated _ as p -> self#unsupported_predicate p
  | Prel (r,t1,t2) -> self#translate_rel r t1 t2
  | Pand (p,q) -> self#translate_and p q
  | Por (p,q) -> self#translate_or p q
  | Pxor _ as p -> self#unsupported_predicate p
  | Pimplies (p,q) -> self#translate_implies p q
  | Piff(p,q) -> self#translate_equiv p q
  | Pnot p -> self#translate_not p
  | Pif(t,p,q) -> self#translate_pif t p q
  | Plet _ as p -> self#unsupported_predicate p
  | Pforall(logic_vars,{content=Pimplies(hyps,goal)}) ->
    self#translate_quantif ~forall:true logic_vars hyps goal
  | Pforall _ as p ->
    Sd_options.Self.warning ~current:true
      "%a not of the form \\forall ...; a ==> b" Printer.pp_predicate p;
    self#unsupported_predicate p
  | Pexists(logic_vars,{content=Pand(hyps,goal)}) ->
    self#translate_quantif ~forall:false logic_vars hyps goal
  | Pexists _ as p ->
    Sd_options.Self.warning ~current:true
      "%a not of the form \\exists ...; a && b" Printer.pp_predicate p;
    self#unsupported_predicate p
  | Pat (p, LogicLabel(_,l)) when l = "Here" -> self#translate_pnamed p
  | Pat _ as p -> self#unsupported_predicate p
  | Pvalid_read (_,t) ->
    Sd_options.Self.warning ~once:true
      "\\valid_read(%a) is interpreted as \\valid(%a)"
      Printer.pp_term t Printer.pp_term t;
    self#translate_valid t
  | Pvalid (_,t) -> self#translate_valid t
  | Pinitialized _ as p -> self#unsupported_predicate p
  | Pspecified _ as p -> self#unsupported_predicate p
  | Pallocable _ as p -> self#unsupported_predicate p
  | Pfreeable _ as p -> self#unsupported_predicate p
  | Pfresh _ as p -> self#unsupported_predicate p
  | Psubtype _ as p -> self#unsupported_predicate p

  (* modify result_varinfo when the function returns something *)
  method private compute_result_varinfo fct =
    let rec do_stmts = function
      | [] -> ()
      | {skind=Return(Some{enode=Lval(Var v,_)},_)}::_ -> result_varinfo<-Some v
      | _ :: t -> do_stmts t
    in
    do_stmts fct.sallstmts

  method private at_least_one_prop kf behaviors kloc =
    let in_ensures b r k =
      r || (List.mem (Property.ip_of_ensures kf kloc b k) props) in
    let in_bhv r b = r || List.fold_left (in_ensures b) false b.b_post_cond in
    List.fold_left in_bhv false behaviors

  method private pre ~pre_entry_point kf behaviors kloc =
    let not_translated p =
      if pre_entry_point then
	Sd_states.Not_Translated_Predicates.fold_left
	  (fun b e -> b || e = p.ip_id) false
      else true
    in
    let translate_as_return pred =
      let ins, v = self#translate_predicate(self#subst_pred pred.ip_content) in
      (* untreated predicates are translated as True *)
      if v <> Ins.one then
	let e = Cil.new_exp ~loc:Ins.loc (UnOp (LNot, v, Cil.intType)) in
	ins @ [Ins.ins_if e [Instru(Ins.instru_ret Ins.zero)] []]
      else ins
    in
    let do_behavior b =
      let requires = List.filter not_translated b.b_requires in
      let typically = List.filter not_translated (Sd_utils.typically_preds b) in
      let to_prop = Property.ip_of_requires kf kloc b in
      let in_props = (fun p -> List.mem (to_prop p) props) in
      let requires = List.filter in_props requires in
      let typically = List.filter in_props typically in
      let do_requires pred =
	if pre_entry_point then translate_as_return pred
	else
	  let prop = to_prop pred in
	  let id = Sd_utils.to_id prop in
	  self#pc_assert_exception pred.ip_content "Pre-condition!" id prop
      in
      let do_typically pred =
	if pre_entry_point then translate_as_return pred else []
      in
      if requires <> [] || typically <> [] then
	let typically = List.map do_typically typically in
	let requires = List.map do_requires requires in
	let inserts' = List.fold_left (@) [] typically in
	let inserts = List.fold_left (@) inserts' requires in
	if b.b_assumes <> [] then
	  let inserts_0, exp = self#cond_of_assumes b.b_assumes in
	  let insert_1 = Ins.ins_if exp inserts [] in
	  inserts_0 @ [insert_1]
	else inserts
      else []
    in
    List.fold_left (@) [] (List.map do_behavior behaviors)

  method private post kf behaviors kloc =
    let do_behavior b =
      let post = b.b_post_cond in
      let to_prop = Property.ip_of_ensures kf kloc b in
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
		  Sd_states.Behavior_Reachability.replace
		    bhv_to_reach_cpt (kf, b, false);
		  bhv_to_reach_cpt <- bhv_to_reach_cpt+1;
		  [Instru(Pc_to_framac str)]
		end
	      else []
	    in
	    let inserts_then_1 =
	      List.fold_left (@) [] (List.map do_postcond post) in
	    let insert_1 = Ins.ins_if exp (inserts_then_0@inserts_then_1) [] in
	    inserts_0 @ [insert_1]
	  else
	    let inserts_0 = 
	      if add_reach_info then
		begin
		  Sd_states.Behavior_Reachability.replace
		    bhv_to_reach_cpt (kf, b, false);
		  bhv_to_reach_cpt <- bhv_to_reach_cpt+1;
		  [Instru(Pc_to_framac str)]
		end
	      else []
	    in
	    let inserts_1 = List.fold_left (@) [] (List.map do_postcond post) in
	    inserts_0 @ inserts_1
	end
      else []
    in
    List.fold_left (@) [] (List.map do_behavior behaviors)

  (* alloc and dealloc variables for \at terms *)
  method private save_varinfo kf varinfo =
    let dig_type = function
      | TPtr(ty,_) | TArray(ty,_,_,_) -> ty
      | ty -> Sd_options.Self.abort "dig_type %a" Printer.pp_typ ty
    in
    let dig_type x = dig_type (Cil.unrollTypeDeep x) in
    let lengths = Sd_utils.lengths_from_requires kf in
    let terms =
      try Cil_datatype.Varinfo.Hashtbl.find lengths varinfo with Not_found -> []
    in
    let do_varinfo v =
      let my_v = v in
      let my_old_v = Ins.my_varinfo v.vtype ("old_"^v.vname) in
      let insert_decl = Ins.decl_varinfo my_old_v in
      let lmy_old_v = Cil.var my_old_v in
      let insert_before = Instru(Ins.instru_affect lmy_old_v (Cil.evar my_v)) in
      let rec alloc_aux my_old_ptr my_ptr ty = function
	| h :: t ->
	  let ty = dig_type ty in
	  let inserts_0, h' = self#translate_term h in
	  let my_iterator = self#fresh_ctype_varinfo Cil.intType in
	  let insert_1 = Ins.decl_varinfo my_iterator in
	  begin
	    match h.term_type with
	    | Linteger ->
	      let tmp = self#fresh_ctype_varinfo Cil.ulongType in
	      let i_1 = Ins.decl_varinfo tmp in
	      let i_2 = Instru(Ins.instru_Z_get_si tmp h') in
	      let loc = Ins.loc in
	      let e_tmp = Cil.evar tmp in
	      let e1 = Cil.new_exp ~loc (SizeOf ty) in
	      let e2 = Cil.mkBinOp ~loc Mult e_tmp e1 in
	      let insert_2 = Instru(Ins.instru_malloc my_old_ptr e2) in
	      let offset = Index(Cil.evar my_iterator, NoOffset) in
	      let my_new_old_ptr = Cil.addOffsetLval offset my_old_ptr in
	      let my_new_ptr = Cil.addOffsetLval offset my_ptr in
	      let inserts_block = alloc_aux my_new_old_ptr my_new_ptr ty t in
	      let lmy_iterator = Cil.var my_iterator in
	      let init = Ins.instru_affect lmy_iterator Ins.zero in
	      let i_3 = Instru(Ins.instru_Z_get_si tmp h') in
	      let e_iterator = Cil.evar my_iterator in
	      let cond = Ins.cmp Rlt e_iterator e_tmp in
	      let e3 = Cil.mkBinOp ~loc PlusA e_iterator Ins.one in
	      let step = Ins.instru_affect lmy_iterator e3 in
	      let insert_3 = Ins.ins_for init cond step inserts_block in
	      let insert_4 = Instru(Ins.instru_Z_clear h') in
	      inserts_0 @ [insert_1; i_1;i_2; insert_2; i_3; insert_3; insert_4]
	    | Lreal -> assert false (* TODO: reals *)
	    | _ ->
	      let loc = Ins.loc in
	      let e1 = Cil.new_exp ~loc (SizeOf ty) in
	      let e2 = Cil.mkBinOp ~loc Mult h' e1 in
	      let insert_2 = Instru(Ins.instru_malloc my_old_ptr e2) in
	      let offset = Index(Cil.evar my_iterator, NoOffset) in
	      let my_new_old_ptr = Cil.addOffsetLval offset my_old_ptr in
	      let my_new_ptr = Cil.addOffsetLval offset my_ptr in
	      let inserts_block = alloc_aux my_new_old_ptr my_new_ptr ty t in
	      let lmy_iterator = Cil.var my_iterator in
	      let e_iterator = Cil.evar my_iterator in
	      let init = Ins.instru_affect lmy_iterator Ins.zero in
	      let cond = Ins.cmp Rlt e_iterator h' in
	      let e3 = Cil.mkBinOp ~loc PlusA e_iterator Ins.one in
	      let step = Ins.instru_affect lmy_iterator e3 in
	      let insert_3 = Ins.ins_for init cond step inserts_block in
	      inserts_0 @ [insert_1; insert_2; insert_3]
	  end
	| [] ->
	  let e = Cil.new_exp ~loc:Ins.loc (Lval my_ptr) in
	  [Instru(Ins.instru_affect my_old_ptr e)]
      in
      if Cil.isPointerType v.vtype || Cil.isArrayType v.vtype then
	let my_old_ptr = Ins.my_varinfo v.vtype ("old_ptr_" ^ v.vname) in
	let insert_0 = Ins.decl_varinfo my_old_ptr in
	let inserts_decl = [insert_decl; insert_0] in
	let ins = alloc_aux (Cil.var my_old_ptr) (Cil.var my_v) v.vtype terms in
	let inserts_before = insert_before :: ins in
	inserts_decl, inserts_before
      else [insert_decl], [insert_before]
    in
    let inserts_decl, inserts_before = do_varinfo varinfo in
    let do_varinfo v =
      let loc = Ins.loc in
      let rec dealloc_aux my_old_ptr = function
	| [] -> []
	| _ :: [] ->
	  let e = Cil.new_exp ~loc (Lval my_old_ptr) in
	  [Instru(Ins.instru_free e)]
	| h :: t ->
	  let my_iterator = self#fresh_ctype_varinfo Cil.intType in
	  let insert_0 = Ins.decl_varinfo my_iterator in
	  let inserts_1, h' = self#translate_term h in
	  let inserts' =
	    match h.term_type with
	    | Linteger ->
	      let offset = Index(Cil.evar my_iterator, NoOffset) in
	      let aux = Cil.addOffsetLval offset my_old_ptr in
	      let inserts_block = dealloc_aux aux t in
	      let lmy_iterator = Cil.var my_iterator in
	      let init = Ins.instru_affect lmy_iterator Ins.zero in
	      let tmp = self#fresh_ctype_varinfo Cil.intType in
	      let i_1 = Ins.decl_varinfo tmp in
	      let i_2 = Instru(Ins.instru_Z_get_si tmp h') in
	      let e_iterator = Cil.evar my_iterator in
	      let e_tmp = Cil.evar tmp in
	      let cond = Ins.cmp Rlt e_iterator e_tmp in
	      let e1 = Cil.mkBinOp ~loc PlusA e_iterator Ins.one in
	      let step = Ins.instru_affect lmy_iterator e1 in
	      let insert_2 = Ins.ins_for init cond step inserts_block in
	      [i_1; i_2; insert_2; Instru(Ins.instru_Z_clear h')]
	    | Lreal -> assert false (* TODO: reals *)
	    | _ ->
	      let offset = Index(Cil.evar my_iterator, NoOffset) in
	      let aux = Cil.addOffsetLval offset my_old_ptr in
	      let inserts_block = dealloc_aux aux t in
	      let lmy_iterator = Cil.var my_iterator in
	      let init = Ins.instru_affect lmy_iterator Ins.zero in
	      let e_iterator = Cil.evar my_iterator in
	      let cond = Ins.cmp Rlt e_iterator h' in
	      let e1 = Cil.mkBinOp ~loc PlusA e_iterator Ins.one in
	      let step = Ins.instru_affect lmy_iterator e1 in
	      [Ins.ins_for init cond step inserts_block]
	  in
	  let e = Cil.new_exp ~loc (Lval my_old_ptr) in
	  [insert_0] @ inserts_1 @ inserts' @ [Instru(Ins.instru_free e)]
      in
      let my_old_ptr = Ins.my_varinfo v.vtype ("old_ptr_" ^ v.vname) in
      dealloc_aux (Cil.var my_old_ptr) terms
    in
    let inserts_after = do_varinfo varinfo in
    inserts_decl, inserts_before, inserts_after

  method! vfunc f =
    let entry_point = Kernel_function.get_name (fst(Globals.entry_point())) in
    let kf = Globals.Functions.find_by_name f.svar.vname in
    let behaviors = Annotations.behaviors kf in
    self#compute_result_varinfo f;
    let label_pre, inserts_pre =
      if f.svar.vname = entry_point then
	BegFunc (f.svar.vname ^ "_precond"),
	self#pre ~pre_entry_point:true kf behaviors Kglobal
      else
	BegFunc f.svar.vname,
	self#pre ~pre_entry_point:false kf behaviors Kglobal
    in
    List.iter (self#insert label_pre) inserts_pre;
    if (self#at_least_one_prop kf behaviors Kglobal)
      || (Sd_options.Behavior_Reachability.get()) then
      begin
	let inserts = self#post kf behaviors Kglobal in
	self#insert (EndFunc f.svar.vname) (Block inserts)
      end;
    let do_varinfo v =
      let inserts_decl,inserts_before,inserts_after = self#save_varinfo kf v in
      List.iter (self#insert (BegFunc f.svar.vname)) inserts_decl;
      List.iter (self#insert (BegFunc f.svar.vname)) inserts_before;
      List.iter (self#insert (EndFunc f.svar.vname)) inserts_after
    in
    List.iter do_varinfo visited_globals;
    List.iter do_varinfo (Kernel_function.get_formals kf);
    Cil.DoChildren
  (* end vfunc *)

  method private subst_pred p = (new Sd_subst.subst)#pred p [] [] [] []

  method private cond_of_assumes ?(subst_pred=self#subst_pred) pred_list =
    let rec aux insertions ret = function
      | [] -> insertions, ret
      | h :: t ->
	let ins, v = self#translate_predicate (subst_pred h.ip_content) in
	let e = Cil.mkBinOp ~loc:Ins.loc LAnd ret v in
	aux (insertions @ ins) e t
    in
    aux [] Ins.one pred_list

  method private cond_of_behaviors pred_lists =
    let rec aux insertions ret = function
      | [] -> insertions, ret
      | h :: t ->
	let ins, v = self#cond_of_assumes h in
	let e = Cil.mkBinOp ~loc:Ins.loc LOr ret v in
	aux (insertions @ ins) e t
    in
    aux [] Ins.zero pred_lists

  method private pc_assert_exception pred msg id prop =
    let inserts_0, var = self#translate_predicate (self#subst_pred pred) in
    let e = Cil.new_exp ~loc:Ins.loc (UnOp(LNot, var, Cil.intType)) in
    let insert_1 = Ins.ins_if e [Instru(Pc_exn(msg, id))] [] in
    translated_properties <- prop :: translated_properties;
    inserts_0 @ [insert_1]

  method private for_behaviors bhvs ins =
    if bhvs <> [] then
      let inserts_0, cond = self#cond_of_behaviors bhvs in
      let insert_1 = Ins.ins_if cond ins [] in
      let inserts = inserts_0 @ [insert_1] in
      inserts
    else ins

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
    let for_behaviors = List.map on_behavior_name bhv_names in
    begin
      match ca.annot_content with
      | AStmtSpec (_,bhvs) ->

	if (self#at_least_one_prop kf bhvs.spec_behavior (Kstmt stmt))
	  || (Sd_options.Behavior_Reachability.get()) then
	  begin
	    let stmt_behaviors = bhvs.spec_behavior in
	    let inserts' =
	      self#pre ~pre_entry_point:false kf stmt_behaviors (Kstmt stmt) in
	    let inserts = self#for_behaviors for_behaviors inserts' in
	    List.iter (self#insert (BegStmt stmt.sid)) inserts;
	    let inserts' = self#post kf stmt_behaviors (Kstmt stmt) in
	    let inserts =
	      if for_behaviors = [] then [Block inserts']
	      else self#for_behaviors for_behaviors inserts'
	    in
	    List.iter (self#insert (EndStmt stmt.sid)) inserts;
	  end

      | AAssert (_,pred) ->

	let prop = Property.ip_of_code_annot_single kf stmt ca in
	if List.mem prop props then
	  let id = Sd_utils.to_id prop in
	  let ins = self#pc_assert_exception pred.content "Assert!" id prop in
	  let inserts = self#for_behaviors for_behaviors ins in
	  List.iter (self#insert (BegStmt stmt.sid)) inserts

      | AInvariant (_,true,pred) ->

	let prop = Property.ip_of_code_annot_single kf stmt ca in
	if List.mem prop props then
	  let id = Sd_utils.to_id prop in
	  let f label msg =
	    let ins = self#pc_assert_exception pred.content msg id prop in
	    let inserts = self#for_behaviors for_behaviors ins in
	    List.iter (self#insert label) inserts
	  in
	  f (BegStmt stmt.sid) "Loop invariant not established!";
	  f (EndIter stmt.sid) "Loop invariant not preserved!"

      | AVariant (term,_) ->

	let prop = Property.ip_of_code_annot_single kf stmt ca in
	if List.mem prop props then
	  let id = Sd_utils.to_id prop in
	  begin
	    match term.term_type with
	    | Linteger ->
	      let inserts_0, term' = self#translate_term term in
	      List.iter (self#insert (BegStmt stmt.sid)) inserts_0;
	      let tmp = self#fresh_ctype_varinfo Cil.intType in
	      let e_tmp = Cil.evar tmp in
	      let i_1 = Ins.decl_varinfo tmp in
	      let i_2 = Instru(Ins.instru_Z_cmp_ui tmp term' Ins.zero) in
	      let instr = Instru(Pc_exn("Variant non positive", id)) in
	      self#insert (BegStmt stmt.sid) i_1;
	      self#insert (BegStmt stmt.sid) i_2;
	      self#insert (BegStmt stmt.sid)
		(Ins.ins_if (Ins.cmp Rlt e_tmp Ins.zero) [instr] []);
	      self#insert (EndStmt stmt.sid) (Instru(Ins.instru_Z_clear term'));
	      let inserts_1, term' = self#translate_term term in
	      List.iter (self#insert (BegIter stmt.sid)) inserts_1;
	      let fresh_variant = self#fresh_Z_varinfo() in
	      let insert_2 = Ins.decl_varinfo fresh_variant in
	      self#insert (BegIter stmt.sid) insert_2;
	      let insert_3 = Instru(Ins.instru_Z_init_set fresh_variant term')in
	      self#insert (BegIter stmt.sid) insert_3;
	      let inserts_4, term' = self#translate_term term in
	      List.iter (self#insert (EndIter stmt.sid)) inserts_4;
	      let e_variant  = Cil.evar fresh_variant in
	      let i_3 = Instru(Ins.instru_Z_cmp_ui tmp e_variant Ins.zero) in
	      let instr = Instru(Pc_exn("Variant non positive", id)) in
	      self#insert (EndIter stmt.sid) i_3;
	      self#insert (EndIter stmt.sid)
		(Ins.ins_if(Ins.cmp Rlt e_tmp Ins.zero) [instr] []);
	      let i_4 = Instru(Ins.instru_Z_cmp tmp term' e_variant) in
	      let instr = Instru(Pc_exn("Variant non decreasing", id)) in
	      self#insert (EndIter stmt.sid) i_4;
	      self#insert (EndIter stmt.sid)
		(Ins.ins_if(Ins.cmp Rge e_tmp Ins.zero) [instr] []);
	      self#insert (EndIter stmt.sid)
		(Instru(Ins.instru_Z_clear e_variant))
	    | Lreal -> assert false (* TODO: reals *)
	    | _ ->
	      let inserts_0, term' = self#translate_term term in
	      List.iter (self#insert (BegStmt stmt.sid)) inserts_0;
	      let cond = Ins.cmp Rlt term' Ins.zero in
	      let instr = Instru(Pc_exn("Variant non positive", id)) in
	      self#insert (BegStmt stmt.sid) (Ins.ins_if cond [instr] []);
	      let inserts_1, term' = self#translate_term term in
	      List.iter (self#insert (BegIter stmt.sid)) inserts_1;
	      let variant = self#fresh_ctype_varinfo Cil.intType in
	      let lvariant = Cil.var variant in
	      self#insert (BegIter stmt.sid) (Ins.decl_varinfo variant);
	      self#insert (BegIter stmt.sid)
		(Instru(Ins.instru_affect lvariant term'));
	      let inserts_2, term' = self#translate_term term in
	      List.iter (self#insert (EndIter stmt.sid)) inserts_2;
	      let e_variant = Cil.evar variant in
	      let cond = Ins.cmp Rlt e_variant Ins.zero in
	      let instr = Instru(Pc_exn("Variant non positive", id)) in
	      self#insert (EndIter stmt.sid) (Ins.ins_if cond [instr] []);
	      let cond = Ins.cmp Rge term' e_variant in
	      let instr = Instru(Pc_exn("Variant non decreasing", id)) in
	      self#insert (EndIter stmt.sid) (Ins.ins_if cond [instr] [])
	  end;
	  translated_properties <- prop :: translated_properties
      | _ -> ()
    end;
    Cil.DoChildren
  (* end vcode_annot *)

  method! vstmt_aux stmt =
    if List.mem stmt.sid stmts_to_reach then
      begin
	let str = Format.sprintf "@@FC:REACHABLE_STMT:%i" stmt.sid in
	self#insert (BegStmt stmt.sid) (Instru(Pc_to_framac str))
      end;
    let kf = Kernel_function.find_englobing_kf stmt in
    match stmt.skind with
    | If(_exp,b1,b2,_loc) ->
      let add_block_reachability b =
	match b.bstmts with
	| first_stmt :: _ ->
	  let dkey = Sd_options.dkey_reach in
      	  Sd_options.Self.debug ~dkey "stmt %i to reach" first_stmt.sid;
	  Sd_states.Unreachable_Stmts.replace first_stmt.sid (first_stmt, kf);
      	  stmts_to_reach <- first_stmt.sid :: stmts_to_reach
      	| _ -> ()
      in
      add_block_reachability b1;
      add_block_reachability b2;
      Cil.DoChildren
    | _ -> Cil.DoChildren

  method! vglob_aux = function
  | GVar(vi,_,_) -> visited_globals <- vi::visited_globals; Cil.DoChildren
  | _ -> Cil.DoChildren
end
