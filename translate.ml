
open Cil_types

exception Unreachable
exception Unsupported


let loc = Cil_datatype.Location.unknown

(* varinfos *)
let my_varinfo ty varname = Cil.makeVarinfo false false varname ty
let my_Z_varinfo s = my_varinfo (Utils.mpz_t()) s

(* expressions *)
let zero = Cil.zero ~loc
let one = Cil.one ~loc
let cmp rel e1 e2 = Cil.mkBinOp ~loc (Utils.relation_to_binop rel) e1 e2

let instru_affect a b = Insertion.mk_instru (Set(a,b,loc))

let no_repeat l =
  let rec aux acc = function
    | [] -> acc
    | h :: t when List.mem h acc -> aux acc t
    | h :: t -> aux (h :: acc) t
  in
  aux  [] l

let rec typename = function
  | TInt (ikind, _) ->
     begin
       match ikind with
       | IBool -> "bool"
       | IChar -> "char"
       | ISChar -> "schar"
       | IUChar -> "uchar"
       | IInt -> "sint"
       | IUInt -> "uint"
       | IShort -> "sshort"
       | IUShort -> "ushort"
       | ILong -> "slong"
       | IULong -> "ulong"
       | ILongLong -> "slonglong"
       | IULongLong -> "ulonglong"
     end
  | TFloat (fkind, _) ->
     begin
       match fkind with
       | FFloat -> "float"
       | FDouble -> "double"
       | FLongDouble -> raise Unsupported
     end
  | TNamed (ty, _) -> typename ty.ttype
  | _ -> raise Unreachable


class gather_insertions props swd = object(self)
  inherit Visitor.frama_c_inplace

  val insertions = Hashtbl.create 64
  val mutable functions = ([] : Function.t list)
  val mutable result_varinfo = None
  val mutable in_old_term = false
  val mutable in_old_ptr = false
  val mutable visited_globals = []
  val last_varname = Datatype.String.Hashtbl.create 64
  val mutable translated_properties = []
  val mutable fcts_called = ([] : varinfo list)

  method get_insertions () = insertions
  method get_functions () = functions
  method get = States.Externals.find
  method private call fct ret args =
    let vi = self#get fct in
    self#add_function_call vi;
    Insertion.mk_instru (Call(ret, Cil.evar vi, args, loc))
  method cmalloc x y = self#call "malloc" (Some x) [y]
  method cfree x = self#call "free" None [x]
  method cpc_dim x y = self#call "pathcrawler_dimension" (Some x) [y]
  method cpc_exc x y = self#call "pathcrawler_assert_exception" None [x;y]
  method cpc_assume x y = self#call "pathcrawler_assume_exception" None [x;y]
  method cpc_to_fc x = self#call "pathcrawler_to_framac" None [x]
  method cclear x = self#call "__gmpz_clear" None [x]
  method cinit x = self#call "__gmpz_init" None [x]
  method cinit_set x y = self#call "__gmpz_init_set" None [x;y]
  method cinit_set_ui x y = self#call "__gmpz_init_set_ui" None [x;y]
  method cinit_set_si x y = self#call "__gmpz_init_set_si" None [x;y]
  method cinit_set_str x y z = self#call "__gmpz_init_set_str" None [x;y;z]
  method cset x y = self#call "__gmpz_set" None [x;y]
  method cabs x y = self#call "__gmpz_abs" None [x;y]
  method cadd x y z = self#call "__gmpz_add" None [x;y;z]
  method cadd_ui x y z = self#call "__gmpz_add_ui" None [x;y;z]
  method csub x y z = self#call "__gmpz_sub" None [x;y;z]
  method csub_ui x y z = self#call "__gmpz_sub_ui" None [x;y;z]
  method cui_sub x y z = self#call "__gmpz_ui_sub" None [x;y;z]
  method cmul x y z = self#call "__gmpz_mul" None [x;y;z]
  method cmul_ui x y z = self#call "__gmpz_mul_ui" None [x;y;z]
  method cmul_si x y z = self#call "__gmpz_mul_si" None [x;y;z]
  method ctdiv_q x y z = self#call "__gmpz_tdiv_q" None [x;y;z]
  method ctdiv_q_ui x y z = self#call "__gmpz_tdiv_q_ui" None [x;y;z]
  method ctdiv_r x y z = self#call "__gmpz_tdiv_r" None [x;y;z]
  method ctdiv_r_ui x y z = self#call "__gmpz_tdiv_r_ui" None [x;y;z]
  method cbinop op x y z =
    self#call("__gmpz_"^(Utils.binop_to_fname op)) None [x;y;z]
  method cbinop_ui op x y z =
    self#call("__gmpz_"^(Utils.binop_to_fname op)^"_ui") None [x;y;z]
  method cget_ui x y = self#call "__gmpz_get_ui" (Some x) [y]
  method cget_si x y = self#call "__gmpz_get_si" (Some x) [y]
  method ccmp x y z = self#call "__gmpz_cmp" (Some x) [y;z]
  method ccmp_ui x y z = self#call "__gmpz_cmp_ui" (Some x) [y;z]
  method ccmp_si x y z = self#call "__gmpz_cmp_si" (Some x) [y;z]
  method cmul_2exp x y z = self#call "__gmpz_mul_2exp" None [x;y;z]
  method cfdiv_q_2exp x y z = self#call "__gmpz_fdiv_q_2exp" None [x;y;z]
  method cnondet ty x = self#call ("nondet_"^(typename ty)) (Some x) []

  method private add_function_call vi =
    if List.mem vi fcts_called then () else fcts_called <- vi :: fcts_called

  method get_new_globals() =
    let on_varinfo ret v =
      try
	(* the nondet values (as an array) of each type *)
	if (String.sub v.vname 0 7) = "nondet_" then
	  let vname1 = v.vname ^ "_val" in
	  let ty1 = TPtr(Cil.getReturnType v.vtype,[]) in
	  let vi1 = Cil.makeVarinfo false false vname1 ty1 in
	  vi1 :: ret
	else ret
      with _ -> ret
    in
    List.fold_left on_varinfo [] fcts_called

  (* those globals are initialized to zero *)
  method get_new_init_globals() =
    let on_varinfo ret v =
      try
	(* the number of nondet values of each type *)
	if (String.sub v.vname 0 7) = "nondet_" then
	  let vname2 = v.vname ^ "_cpt" in
	  let vi2 = Cil.makeVarinfo false false vname2 Cil.uintType in
	  vi2 :: ret
	else ret
      with _ -> ret
    in
    List.fold_left on_varinfo [] fcts_called

  method private insert label str =
    try Queue.add str (Hashtbl.find insertions label)
    with Not_found ->
      let q = Queue.create() in
      Queue.add str q;
      Hashtbl.add insertions label q

  method private fresh_varinfo ty varname =
    let varname = "__sd_" ^ varname in
    let i =
      try (Datatype.String.Hashtbl.find last_varname varname)+1
      with Not_found -> 0
    in
    let v = my_varinfo ty (varname ^ "_" ^ (string_of_int i)) in
    Datatype.String.Hashtbl.replace last_varname varname i;
    v

  method private fresh_Z_varinfo varname =
    self#fresh_varinfo (Utils.mpz_t()) ("Z_" ^ varname)

  method private fresh_ctype_varinfo ty varname = self#fresh_varinfo ty varname

  method private fresh_pred_varinfo varname =
    self#fresh_varinfo Cil.intType varname

  method private fresh_fct_varinfo ty varname = self#fresh_varinfo ty varname

  method translated_properties() = no_repeat translated_properties

  method private translate_constant ty = function
    | Integer (i, str_opt) ->
       begin
	 match ty with
	 | Linteger ->
	    let fresh_var = self#fresh_Z_varinfo "cst" in
	    let i_0 = Insertion.mk_decl fresh_var in
	    let str = try Extlib.the str_opt with _ -> Integer.to_string i in
	    let str = Cil.mkString ~loc str in
	    let e_var = Cil.evar fresh_var in
	    let ten = CInt64(Integer.of_int 10, Cil_types.IInt, Some "10") in
	    let e_ten = Cil.new_exp ~loc (Const ten) in
	    let i_1 = self#cinit_set_str e_var str e_ten in
	    [i_0; i_1], Cil.evar fresh_var
	 | Ctype(TInt(ik,_)) ->[],Cil.new_exp ~loc (Const(CInt64(i,ik,str_opt)))
	 | _ -> raise Unreachable
       end
    | LStr str -> [], Cil.new_exp ~loc (Const(CStr str))
    | LWStr i64_l -> [], Cil.new_exp ~loc (Const(CWStr i64_l))
    | LChr c -> [], Cil.new_exp ~loc (Const(CChr c))
    | LReal {r_literal=s; r_nearest=f; r_lower=l; r_upper=u} ->
       if l <> u then
	 Options.warning ~current:true ~once:true
			 "approximating a real number by a float";
       [], Cil.new_exp ~loc (Const(CReal(f, FLongDouble, Some s)))
    | LEnum e -> [], Cil.new_exp ~loc (Const(CEnum e))

  method private translate_var lv =
    let varname = match self#current_func with
      | Some _ when in_old_term ->
	 let prefix = match lv.lv_type with
	   | Ctype ty when (Cil.isPointerType ty || Cil.isArrayType ty)
			   && in_old_ptr -> "old_ptr"
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
    | Linteger -> my_Z_varinfo varname
    | Lreal -> raise Unsupported
    | Ctype ty -> my_varinfo ty varname
    | _ -> raise Unreachable

  method private translate_unop op t = match t.term_type with
    | Linteger ->
       assert(op = Neg);
       let i_0, e = self#translate_term t in
       let ret = self#fresh_Z_varinfo "neg" in
       let i_1 = Insertion.mk_decl ret in
       let e_ret = Cil.evar ret in
       let i_2 = self#cinit e_ret in
       let i_3 = self#cui_sub e_ret zero e in
       let i_4 = self#cclear e in
       i_0 @ [i_1; i_2; i_3; i_4], Lval(Cil.var ret)
    | Lreal -> raise Unsupported
    | _ -> let ins, e = self#translate_term t in ins, UnOp(op,e,(Cil.typeOf e))

  method private translate_shift ty varname shift a b = match ty with
    | Linteger ->
       let ret = self#fresh_Z_varinfo varname in
       let e_ret = Cil.evar ret in
       let i_0 = Insertion.mk_decl ret in
       let i_1 = self#cinit e_ret in
       let i_2, x = self#as_logic_type Linteger a in
       let i_3, y = self#as_c_type Cil.ulongLongType b in
       let i_4 = shift e_ret x y in
       let i_5 = self#cclear x in
       i_0 :: i_1 :: i_2 @ i_3 @ [i_4 ; i_5], e_ret.enode
    | _ -> raise Unreachable

  method private translate_binop ty op a b = match op with
    | IndexPI
    | PlusPI
    | MinusPI ->
       let i_0, a' = self#translate_term a in
       let i_1, b' = self#as_c_type Cil.intType b in
       let e' = Cil.new_exp ~loc (BinOp(op,a',b',(Cil.typeOf a'))) in
       i_0 @ i_1, e'.enode
    | Shiftlt -> self#translate_shift ty "lshift" self#cmul_2exp a b
    | Shiftrt -> self#translate_shift ty "rshift" self#cfdiv_q_2exp a b
    | _ ->
       match ty with
       | Linteger ->
	  let i_0, x = self#as_logic_type Linteger a in
	  let i_1, y = self#as_logic_type Linteger b in
	  let ret = self#fresh_Z_varinfo (Utils.binop_to_fname op) in
	  let i_2 = Insertion.mk_decl ret in
	  let e_ret = Cil.evar ret in
	  let i_3 = self#cinit e_ret in
	  let clear_t1 = self#cclear x in
	  let clear_t2 = self#cclear y in
	  let i_4 = self#cbinop op e_ret x y in
	  i_0 @ i_1 @ [i_2 ; i_3 ; i_4 ; clear_t1; clear_t2 ], e_ret.enode
       | Lreal -> raise Unsupported
       | Ltype _ as lt when Logic_const.is_boolean_type lt ->
	  let i_0, x = self#translate_term a in
	  let i_1, y = self#translate_term b in
	  let inserts, e =
	    match a.term_type, b.term_type with
	    | Linteger, Linteger ->
	       let var = self#fresh_ctype_varinfo Cil.intType "binop" in
	       let i_2 = Insertion.mk_decl var in
	       let tmp = self#fresh_ctype_varinfo Cil.intType "binop_cmp" in
	       let e_tmp = Cil.evar tmp in
	       let i_3 = Insertion.mk_decl tmp in
	       let i_4 = self#ccmp (Cil.var tmp) x y in
	       let op = Utils.binop_to_relation op in
	       let lvar = Cil.var var in
	       let i_5 = instru_affect lvar (cmp op e_tmp zero) in
	       let i_6 = self#cclear x in
	       let i_7 = self#cclear y in
	       [i_2; i_3; i_4; i_5; i_6; i_7], Cil.evar var
	    | _ -> [], Cil.mkBinOp ~loc op x y
	  in
	  i_0 @ i_1 @ inserts, e.enode
       | _ -> raise Unreachable

  method private translate_tif cond then_b else_b = match then_b.term_type with
    | Linteger ->
       let ret = self#fresh_Z_varinfo "tif" in
       let i_0 = Insertion.mk_decl ret in
       let e_ret = Cil.evar ret in
       let i_1 = self#cinit e_ret in
       let i_2, cond' = self#translate_term cond in
       let tmp = self#fresh_ctype_varinfo Cil.intType "tif_cmp" in
       let e_tmp = Cil.evar tmp in
       let i_3 = Insertion.mk_decl tmp in
       let i_4 = self#ccmp_si (Cil.var tmp) cond' zero in
       let inserts_then_0, then_b' = self#translate_term then_b in
       let set_1 = self#cset e_ret then_b' in
       let clear_1 = self#cclear then_b' in
       let i_then = inserts_then_0 @ [set_1 ; clear_1] in
       let inserts_else_0, else_b' = self#translate_term else_b in
       let set_2 = self#cset e_ret else_b' in
       let clear_2 = self#cclear else_b' in
       let i_else = inserts_else_0 @ [ set_2 ; clear_2] in
       let i_5 = Insertion.mk_if (cmp Rneq e_tmp zero) i_then i_else in
       let i_6 = self#cclear cond' in
       i_0 :: i_1 :: i_2 @ [i_3; i_4; i_5; i_6], e_ret.enode
    | Lreal -> raise Unsupported
    | _ -> raise Unreachable

  method private translate_at t = function
    | LogicLabel(_,stringlabel) ->
       if stringlabel = "Old" || stringlabel = "Pre" then
	 let is_ptr =
	   match t.term_node with TLval(TMem _,_) -> true | _-> false in
	 if is_ptr then in_old_ptr <- true;
	 in_old_term <- true;
	 let ins, v = self#translate_term t in
	 if is_ptr then in_old_ptr <- false;
	 in_old_term <- false;
	 ins, v.enode
	 else
	   (* label Post is only encoutered in post-conditions, and \at(t,Post)
	    * in a post-condition is t *)
	   if stringlabel = "Post" || stringlabel = "Here" then
	     let ins, v = self#translate_term t in
	     ins, v.enode
	   else
	     Options.not_yet_implemented
	       "Sd_insertions.gather_insertions#term_node \\at(%a,%s)"
	       Debug.pp_term t stringlabel
    | _ -> raise Unsupported

  (* C type -> logic type *)
  method private translate_logic_coerce lt t = match lt with
    | Linteger ->
       let ty = match t.term_type with
	 | Ctype x -> Ctype (Cil.unrollType x)
	 | x -> x
       in
       let i_0, v = self#translate_term t in
       let ret = self#fresh_Z_varinfo "to_Z" in
       let i_1 = Insertion.mk_decl ret in
       let init_set = match ty with
	 | Ctype x when Cil.isUnsignedInteger x -> self#cinit_set_ui
	 | Ctype x when Cil.isSignedInteger x -> self#cinit_set_si
	 | _ -> raise Unsupported
       in
       let e_ret = Cil.evar ret in
       let i_2 = init_set e_ret v in
       i_0 @ [i_1; i_2], e_ret.enode
    | Lreal -> raise Unsupported
    | _ -> raise Unreachable

  (* logic type -> C type *)
  method private translate_coerce t ty = match t.term_type with
    | Linteger ->
       let i_0, v = self#translate_term t in
       let ret = self#fresh_ctype_varinfo ty "to_ctype" in
       let i_1 = Insertion.mk_decl ret in
       let get = match ty with
	 | x when Cil.isUnsignedInteger x -> self#cget_ui
	 | x when Cil.isSignedInteger x -> self#cget_si
	 | _ -> raise Unsupported
       in
       let i_2 = get (Cil.var ret) v in
       let i_3 = self#cclear v in
       i_0 @ [i_1; i_2; i_3], (Cil.evar ret).enode
    | Lreal -> raise Unsupported
    | _ -> raise Unreachable

  method private as_logic_type ty t = match ty with
    | x when x = t.term_type -> self#translate_term t
    | _ -> let i, e = self#translate_logic_coerce ty t in i, Cil.new_exp ~loc e

  method private as_c_type ty t = match ty with
    | x when Ctype x = t.term_type -> self#translate_term t
    | _ -> let i, e = self#translate_coerce t ty in i, Cil.new_exp ~loc e

  method private translate_lambda li lower upper q t =
    assert(lower.term_type = Linteger && upper.term_type = Linteger);
    let name = li.l_var_info.lv_name in
    let do_op op r l = self#cbinop op r r l in
    let init_val, varname, compute, clear = match name with
      | "\\sum" -> zero, "sum", (do_op PlusA), (fun l -> [self#cclear l])
      | "\\product" -> one, "product", (do_op Mult), (fun l -> [self#cclear l])
      | "\\numof" ->
	 zero, "numof",
	 (fun r l ->
	 Insertion.mk_if (cmp Rneq l zero) [self#cbinop_ui PlusA r r one] []),
	 (fun _ -> [])
      | _ -> raise Unsupported
    in
    let ret = self#fresh_Z_varinfo varname in
    let i_0 = Insertion.mk_decl ret in
    let e_ret = Cil.evar ret in
    let i_1 = self#cinit_set_si e_ret init_val in
    let i_3, low = self#translate_term lower in
    let i_4, up = self#translate_term upper in
    let fresh_iter = my_Z_varinfo q.lv_name in
    let i_5 = Insertion.mk_decl fresh_iter in
    let e_iter = Cil.evar fresh_iter in
    let i_6 = self#cinit_set e_iter low in
    let ins_b_0, lambda_t = self#translate_term t in
    let ins_b_2 = self#cbinop_ui PlusA e_iter e_iter one in
    let tmp = self#fresh_ctype_varinfo Cil.intType (varname ^ "_cmp") in
    let e_tmp = Cil.evar tmp in
    let ii_1 = Insertion.mk_decl tmp in
    let ii_2 = self#ccmp (Cil.var tmp) e_iter up in
    let ii_3 = self#ccmp (Cil.var tmp) e_iter up in
    let ins_b_1 = compute e_ret lambda_t in
    let clear_lambda = clear lambda_t in
    let ins_b = ins_b_0 @ ins_b_1 :: ins_b_2 :: ii_3 :: clear_lambda in
    let i_7 = Insertion.mk_loop (cmp Rle e_tmp zero) ins_b in
    let i_8 = self#cclear e_iter in
    let i_9 = self#cclear low in
    let i_10 = self#cclear up in
    let ins_block = i_3 @ i_4 @ [i_5; i_6; ii_1; ii_2; i_7; i_8; i_9; i_10] in
    [i_0; i_1; Insertion.mk_block ins_block], e_ret.enode

  method private translate_app li _ params =
    let s = li.l_var_info.lv_name in
    let ty = Extlib.the li.l_type in
    match ty, params, s with
    | Linteger, [param], "\\abs" ->
       let i_0, x = self#translate_term param in
       let ret = self#fresh_Z_varinfo "abs" in
       let i_1 = Insertion.mk_decl ret in
       let e_ret = Cil.evar ret in
       let i_2 = self#cinit e_ret in
       let i_3 = self#cabs e_ret x in
       let i_4 = self#cclear x in
       i_0 @ [i_1; i_2; i_3; i_4], e_ret.enode
    | Linteger, [l;u;{term_node=Tlambda([q],t)}], "\\sum"
    | Linteger, [l;u;{term_node=Tlambda([q],t)}], "\\product"
    | Linteger, [l;u;{term_node=Tlambda([q],t)}], "\\numof" ->
       self#translate_lambda li l u q t
    | Linteger, _, _ -> raise Unsupported
    | Lreal, _, _ -> raise Unsupported
    | _ -> raise Unreachable

  method private translate_cast ty t = match t.term_type with (* source type *)
    | Linteger ->
       let i_0, e = self#translate_term t in
       let ret = self#fresh_ctype_varinfo ty "cast" in
       let i_1 = Insertion.mk_decl ret in
       let get = match ty with (* dest type *)
	 | x when Cil.isUnsignedInteger x -> self#cget_ui
	 | x when Cil.isSignedInteger x -> self#cget_si
	 | _ -> raise Unsupported
       in
       let i_2 = get (Cil.var ret) e in
       let i_3 = self#cclear e in
       i_0 @ [i_1; i_2; i_3], (Cil.evar ret).enode
    | Lreal -> raise Unsupported
    | Ctype _ -> let ins, e = self#translate_term t in ins, CastE (ty, e)
    | _ -> raise Unreachable

  method private translate_term_node t = match t.term_node with
    | TConst c -> let i, e = self#translate_constant t.term_type c in i, e.enode
    | TLval tl -> let ins, lv = self#translate_lval tl in ins, Lval lv
    | TSizeOf ty -> [], SizeOf ty
    | TSizeOfE t -> let ins, e = self#translate_term t in ins, SizeOfE e
    | TSizeOfStr str -> [], SizeOfStr str
    | TAlignOf ty -> [], AlignOf ty
    | TAlignOfE t -> let ins, e = self#translate_term t in ins, AlignOfE e
    | TUnOp (op,t) -> self#translate_unop op t
    | TBinOp (op,a,b) -> self#translate_binop t.term_type op a b
    | TCastE (ty,t) -> self#translate_cast ty t
    | TAddrOf (TMem x, TIndex (y, TNoOffset)) ->
       let x' = Cil.mkTermMem ~addr:x ~off:TNoOffset in
       let rec type_of_pointed = function
	 | Ctype (TPtr (ty,_)) -> Ctype ty
	 | Ctype (TArray (ty,_,_,_)) -> Ctype ty
	 | Ctype (TNamed (x,_)) -> type_of_pointed (Ctype x.ttype)
	 | ty ->
	    Options.feedback
	      ~current:true "unsupported type %a" Printer.pp_logic_type ty;
	    raise Unsupported
       in
       let ty = type_of_pointed (Cil.typeOfTermLval x') in
       let x' = Logic_const.term (TLval x') ty in
       self#translate_term_node {t with term_node=(TBinOp(PlusPI,x',y))}
    | TAddrOf tl -> let ins, lv = self#translate_lval tl in ins, AddrOf lv
    | TStartOf tl -> let ins, lv = self#translate_lval tl in ins, StartOf lv
    | Tapp (li,ll,params) -> self#translate_app li ll params
    | Tif (x,y,z) -> self#translate_tif x y z
    | Tat (t,l) -> self#translate_at t l
    | Tnull -> [], zero.enode
    | TLogic_coerce (lt,t) -> self#translate_logic_coerce lt t
    | TCoerce (t,ty) -> self#translate_coerce t ty
    | TCoerceE (t, {term_type=Ctype ty}) -> self#translate_coerce t ty
    | TCoerceE (t, {term_type=lt}) -> self#translate_logic_coerce lt t
    | Tlambda _
    | TDataCons _
    | Tbase_addr _
    | Toffset _
    | Tblock_length _
    | TUpdate _
    | Ttypeof _
    | Ttype _
    | Tempty_set
    | Tunion _
    | Tinter _
    | Tcomprehension _
    | Trange _
    | Tlet _ -> raise Unsupported

  method private translate_term t =
    let ins, enode = self#translate_term_node t in
    ins, Cil.new_exp ~loc enode

  method private translate_lhost = function
    | TVar lv -> [], Var(self#translate_var lv)
    | TResult _ -> [], Var (Extlib.the result_varinfo)
    | TMem t -> let ins, t = self#translate_term t in ins, Mem t

  method private translate_offset = function
    | TNoOffset -> [], NoOffset
    | TField(fi,o) -> let ins, o' = self#translate_offset o in ins, Field(fi,o')
    | TModel _ -> raise Unsupported
    | TIndex(t,o) ->
       let ins, e = self#as_c_type Cil.intType t in
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
       let fresh_var = self#fresh_Z_varinfo "lval" in
       let ins_0, t' = aux() in
       let ins_1 = Insertion.mk_decl fresh_var in
       let e_t' = Cil.new_exp ~loc (Lval t') in
       let e_fresh_var = Cil.evar fresh_var in
       let ins_2 = self#cinit_set e_fresh_var e_t' in
       ins_0 @ [ins_1; ins_2], Cil.var fresh_var
    | Lreal -> raise Unsupported
    | _ -> aux()

  method private translate_predicate p =
    self#translate_predicate_node p.pred_content

  method private translate_rel rel t1 t2 = match t1.term_type, t2.term_type with
    | Linteger, Ctype x ->
       let inserts_0, t1' = self#translate_term t1 in
       let inserts_1, t2' = self#translate_term t2 in
       let varname = Utils.relation_to_string rel in
       let var = self#fresh_ctype_varinfo Cil.intType varname in
       let i_2 = Insertion.mk_decl var in
       let zcmp =
	 if Cil.isUnsignedInteger x then self#ccmp_ui
	 else if Cil.isSignedInteger x then self#ccmp_si
	 else raise Unsupported
       in
       let i_3 = zcmp (Cil.var var) t1' t2' in
       inserts_0 @ inserts_1 @ [i_2; i_3; self#cclear t1'],
       cmp rel (Cil.evar var) zero
    | Lreal, Lreal -> raise Unsupported
    | Linteger, Linteger
    | Ctype _, Linteger ->
       let inserts_0, t1' = self#as_logic_type Linteger t1 in
       let inserts_1, t2' = self#translate_term t2 in
       let varname = Utils.relation_to_string rel in
       let var = self#fresh_ctype_varinfo Cil.intType varname in
       let i_4 = Insertion.mk_decl var in
       let i_5 = self#ccmp (Cil.var var) t1' t2' in
       let i_6 = self#cclear t1' in
       let i_7 = self#cclear t2' in
       inserts_0 @ inserts_1 @ [i_4; i_5; i_6; i_7], cmp rel (Cil.evar var) zero
    | _ ->
       let inserts_0, t1' = self#translate_term t1 in
       let inserts_1, t2' = self#translate_term t2 in
       inserts_0 @ inserts_1, cmp rel t1' t2'

  method private translate_and p q =
    let var = self#fresh_pred_varinfo "and" in
    let inserts_0, pred1_var = self#translate_predicate p in
    let insert_1 = Insertion.mk_decl var in
    let lvar = Cil.var var in
    let insert_2 = instru_affect lvar pred1_var in
    let inserts_b_0, pred2_var = self#translate_predicate q in
    let insert_b_1 = instru_affect lvar pred2_var in
    let e_var = Cil.evar var in
    let insert_3 = Insertion.mk_if e_var (inserts_b_0 @ [insert_b_1]) [] in
    inserts_0 @ [insert_1; insert_2; insert_3], e_var

  method private translate_or p q =
    let var = self#fresh_pred_varinfo "or"  in
    let inserts_0, pred1_var = self#translate_predicate p in
    let insert_1 = Insertion.mk_decl var in
    let lvar = Cil.var var in
    let insert_2 = instru_affect lvar pred1_var in
    let inserts_b_0, pred2_var = self#translate_predicate q in
    let insert_b_1 = instru_affect lvar pred2_var in
    let e_var = Cil.evar var in
    let insert_3 = Insertion.mk_if e_var [] (inserts_b_0 @ [insert_b_1]) in
    inserts_0 @ [insert_1; insert_2; insert_3], e_var

  method private translate_implies p q =
    let var = self#fresh_pred_varinfo "implies" in
    let insert_0 = Insertion.mk_decl var in
    let lvar = Cil.var var in
    let insert_1 = instru_affect lvar one in
    let inserts_2, pred1_var = self#translate_predicate p in
    let inserts_b_0, pred2_var = self#translate_predicate q in
    let insert_b_1 = instru_affect lvar pred2_var in
    let insert_3 = Insertion.mk_if pred1_var (inserts_b_0 @ [insert_b_1]) [] in
    insert_0 :: insert_1 :: inserts_2 @ [insert_3], Cil.evar var

  method private translate_equiv p q =
    let inserts_0, pred1_var = self#translate_predicate p in
    let inserts_1, pred2_var = self#translate_predicate q in
    let not_pred1_var = Cil.new_exp ~loc (UnOp(LNot, pred1_var, Cil.intType)) in
    let not_pred2_var = Cil.new_exp ~loc (UnOp(LNot, pred2_var, Cil.intType)) in
    let exp1 = Cil.mkBinOp ~loc LOr not_pred1_var pred2_var in
    let exp2 = Cil.mkBinOp ~loc LOr not_pred2_var pred1_var in
    inserts_0 @ inserts_1, Cil.mkBinOp ~loc LAnd exp1 exp2

  method private translate_not p =
    let ins, p' = self#translate_predicate p in
    ins, Cil.new_exp ~loc (UnOp(LNot, p', Cil.intType))

  method private translate_pif t p q =
    let inserts_0, t_var = self#translate_term t in
    let res_var = self#fresh_pred_varinfo "pif" in
    let insert_1 = Insertion.mk_decl res_var in
    let cond, ii, insert_3 = match t.term_type with
      | Linteger ->
	 let tmp = self#fresh_ctype_varinfo Cil.intType "pif_cmp" in
	 let i_1 = Insertion.mk_decl tmp in
	 let i_2 = self#ccmp_si (Cil.var tmp) t_var zero in
	 cmp Rneq (Cil.evar tmp) zero, [i_1; i_2], [self#cclear t_var]
      | Lreal -> raise Unsupported
      | Ctype (TInt _) -> cmp Rneq t_var zero, [], []
      | Ltype _ as lt when Logic_const.is_boolean_type lt ->
	 cmp Rneq t_var zero, [], []
      | _ -> raise Unreachable
    in
    let inserts_then_0, pred1_var = self#translate_predicate p in
    let lres_var = Cil.var res_var in
    let insert_then_1 = instru_affect lres_var pred1_var in
    let inserts_then = inserts_then_0 @ [insert_then_1] in
    let inserts_else_0, pred2_var = self#translate_predicate q in
    let insert_else_1 = instru_affect lres_var pred2_var in
    let inserts_else = inserts_else_0 @ [insert_else_1] in
    let insert_2 = Insertion.mk_if cond inserts_then inserts_else in
    inserts_0 @ ii @ insert_1 :: insert_2 :: insert_3, Cil.evar res_var

  method private translate_valid term = match term.term_node with
    | Tempty_set -> [], one
    | TBinOp ((PlusPI|IndexPI),p,{term_node = Trange(Some x,Some y)}) ->
       self#translate_valid_ptr_range p x y
    | TBinOp ((PlusPI|IndexPI),p,x) -> self#translate_valid_ptr_offset p x
    | TBinOp (MinusPI,p,x) ->
       let einfo = {exp_type=x.term_type; exp_name=[]} in
       let x = Cil.term_of_exp_info loc (TUnOp(Neg,x)) einfo in
       self#translate_valid_ptr_offset p x
    | TLval _ -> self#translate_valid_ptr term
    | TAddrOf (TMem x, TIndex (y, TNoOffset)) ->
       let x' = Cil.mkTermMem ~addr:x ~off:TNoOffset in
       let rec type_of_pointed = function
	 | Ctype (TPtr (ty,_)) -> Ctype ty
	 | Ctype (TArray (ty,_,_,_)) -> Ctype ty
	 | Ctype (TNamed (x,_)) -> type_of_pointed (Ctype x.ttype)
	 | ty ->
	    Options.feedback
	      ~current:true "unsupported type %a" Printer.pp_logic_type ty;
	    raise Unsupported
       in
       let ty = type_of_pointed (Cil.typeOfTermLval x') in
       let x' = Logic_const.term (TLval x') ty in
       self#translate_valid {term with term_node=(TBinOp(PlusPI,x',y))}
    | TAddrOf (TVar x, TIndex (y, TNoOffset) as v) ->
       let ty = Cil.typeOfTermLval v in
       let x' = Logic_const.term (TLval (TVar x, TNoOffset)) ty in
       self#translate_valid {term with term_node=(TBinOp(PlusPI,x',y))}
    | TStartOf _ -> self#translate_valid_ptr term
    | _ -> Utils.error_term term

  method private translate_valid_ptr_range pointer min_off max_off =
    let inserts_0, x' = self#translate_term pointer in
    let inserts_1, low_o = self#translate_term min_off in
    let inserts_2, up_o = self#translate_term max_off in
    let ret = self#fresh_pred_varinfo "valid" in
    let l_ret = Cil.var ret in
    let e_ret = Cil.evar ret in
    let i_0 = Insertion.mk_decl ret in
    let dim = self#fresh_ctype_varinfo Cil.intType "valid_dim" in
    let l_dim = Cil.var dim in
    let e_dim = Cil.evar dim in
    let i_before, i_then, cond, i_after =
      match min_off.term_type, max_off.term_type with
      | Linteger, Linteger ->
  	 let nonempty_set = self#fresh_pred_varinfo "valid_cmp" in
  	 let i_8 = Insertion.mk_decl nonempty_set in
  	 let l_nonempty_set = Cil.var nonempty_set in
  	 let e_nonempty_set = Cil.evar nonempty_set in
  	 let i_9 = self#ccmp l_nonempty_set low_o up_o in
  	 let cond = cmp Rle e_nonempty_set zero in
  	 let i_1 = Insertion.mk_decl dim in
  	 let i_2 = self#cpc_dim l_dim x' in
  	 let cmp_dim_off = self#fresh_ctype_varinfo Cil.intType "valid_cmp" in
  	 let l_cmp_dim_off = Cil.var cmp_dim_off in
  	 let e_cmp_dim_off = Cil.evar cmp_dim_off in
  	 let i_3 = Insertion.mk_decl cmp_dim_off in
  	 let i_4 = self#ccmp_ui l_cmp_dim_off up_o e_dim in
  	 let cmp_off_zero = self#fresh_ctype_varinfo Cil.intType "valid_cmp" in
  	 let l_cmp_off_zero = Cil.var cmp_off_zero in
  	 let e_cmp_off_zero = Cil.evar cmp_off_zero in
  	 let i_5 = Insertion.mk_decl cmp_off_zero in
  	 let i_6 = self#ccmp_ui l_cmp_off_zero up_o zero in
  	 let e1 = cmp Rge e_cmp_off_zero zero in
  	 let e2 = cmp Rlt e_cmp_dim_off zero in
	 let e_binop = Cil.mkBinOp ~loc LAnd e1 e2 in
  	 let i_7 = instru_affect l_ret e_binop in
  	 let i_cl = self#cclear low_o in
	 let i_cl2 = self#cclear up_o in
  	 [i_8; i_9], [i_1; i_2; i_3; i_4; i_5; i_6; i_7], cond, [i_cl; i_cl2]
      | Linteger, Ctype (TInt _) ->
  	 let nonempty = self#fresh_pred_varinfo "valid_cmp" in
  	 let i_0' = Insertion.mk_decl nonempty in
  	 let l_nonempty = Cil.var nonempty in
  	 let e_nonempty = Cil.evar nonempty in
  	 let i_cond = self#ccmp_si l_nonempty low_o up_o in
  	 let cond = cmp Rle e_nonempty zero in
  	 let i_1 = Insertion.mk_decl dim in
  	 let i_2 = self#cpc_dim l_dim x' in
  	 let e1 = cmp Rge up_o zero in
  	 let e2 = cmp Rgt e_dim up_o in
	 let e_binop = Cil.mkBinOp ~loc LAnd e1 e2 in
  	 let i_7 = instru_affect l_ret e_binop in
  	 let i_clear = self#cclear low_o in
  	 [i_0'; i_cond], [i_1; i_2; i_7], cond, [i_clear]
      | Ctype (TInt _), Linteger ->
	 let nonempty = self#fresh_pred_varinfo "valid_cmp" in
  	 let i_0' = Insertion.mk_decl nonempty in
  	 let l_nonempty = Cil.var nonempty in
  	 let e_nonempty = Cil.evar nonempty in
  	 let i_cond = self#ccmp_ui l_nonempty up_o low_o in
  	 let cond = cmp Rge e_nonempty zero in
  	 let i_1 = Insertion.mk_decl dim in
  	 let i_2 = self#cpc_dim l_dim x' in
  	 let cmp_dim_off = self#fresh_ctype_varinfo Cil.intType "valid_cmp" in
  	 let l_cmp_dim_off = Cil.var cmp_dim_off in
  	 let e_cmp_dim_off = Cil.evar cmp_dim_off in
  	 let i_3 = Insertion.mk_decl cmp_dim_off in
  	 let i_4 = self#ccmp_ui l_cmp_dim_off up_o e_dim in
  	 let cmp_off_zero = self#fresh_ctype_varinfo Cil.intType "valid_cmp" in
  	 let l_cmp_off_zero = Cil.var cmp_off_zero in
  	 let e_cmp_off_zero = Cil.evar cmp_off_zero in
  	 let i_5 = Insertion.mk_decl cmp_off_zero in
  	 let i_6 = self#ccmp_ui l_cmp_off_zero up_o zero in
  	 let e1 = cmp Rge e_cmp_off_zero zero in
  	 let e2 = cmp Rlt e_cmp_dim_off zero in
	 let e_binop = Cil.mkBinOp ~loc LAnd e1 e2 in
  	 let i_7 = instru_affect l_ret e_binop in
	 let i_clear = self#cclear up_o in
  	 [i_0'; i_cond], [i_1; i_2; i_3; i_4; i_5; i_6; i_7], cond, [i_clear]
      | Ctype (TInt _), Ctype (TInt _) ->
  	 let i_1 = Insertion.mk_decl dim in
  	 let i_2 = self#cpc_dim l_dim x' in
  	 let e1 = cmp Rge up_o zero in
  	 let e2 = cmp Rgt e_dim up_o in
	 let e_binop = Cil.mkBinOp ~loc LAnd e1 e2 in
  	 let i_3 = instru_affect l_ret e_binop in
	 [], [i_1; i_2; i_3], cmp Rle low_o up_o, []
      | _ -> raise Unreachable
    in
    let i_if = Insertion.mk_if cond i_then [instru_affect l_ret one] in
    inserts_0 @ inserts_1 @ inserts_2 @ [i_0] @ i_before @ i_if::i_after, e_ret

  method private translate_valid_ptr_offset pointer offset =
    let loc = pointer.term_loc in
    let inserts_0, x' = self#translate_term pointer in
    let inserts_1, y' = self#translate_term offset in
    let ret = self#fresh_pred_varinfo "valid" in
    let l_ret = Cil.var ret in
    let e_ret = Cil.evar ret in
    let i_0 = Insertion.mk_decl ret in
    let dim = self#fresh_ctype_varinfo Cil.intType "valid_dim" in
    let l_dim = Cil.var dim in
    let e_dim = Cil.evar dim in
    let i_1 = Insertion.mk_decl dim in
    let i_2 = self#cpc_dim l_dim x' in
    let inserts = match offset.term_type with
      | Linteger ->
  	 let cmp_dim_off = self#fresh_ctype_varinfo Cil.intType "valid_cmp" in
  	 let l_cmp_dim_off = Cil.var cmp_dim_off in
  	 let e_cmp_dim_off = Cil.evar cmp_dim_off in
  	 let i_3 = Insertion.mk_decl cmp_dim_off in
  	 let i_4 = self#ccmp_ui l_cmp_dim_off y' e_dim in
  	 let cmp_off_zero = self#fresh_ctype_varinfo Cil.intType "valid_cmp" in
  	 let l_cmp_off_zero = Cil.var cmp_off_zero in
  	 let e_cmp_off_zero = Cil.evar cmp_off_zero in
  	 let i_5 = Insertion.mk_decl cmp_off_zero in
  	 let i_6 = self#ccmp_ui l_cmp_off_zero y' zero in
  	 let e1 = cmp Rge e_cmp_off_zero zero in
  	 let e2 = cmp Rlt e_cmp_dim_off zero in
	 let e_binop = Cil.mkBinOp ~loc LAnd e1 e2 in
  	 let i_7 = instru_affect l_ret e_binop in
  	 let i_clear = self#cclear y' in
  	 [i_3; i_4; i_5; i_6; i_7; i_clear]
      | Ctype (TInt _) ->
  	 let e1 = cmp Rge y' zero in
  	 let e2 = cmp Rgt e_dim y' in
  	 [ instru_affect l_ret (Cil.mkBinOp ~loc LAnd e1 e2) ]
      | _ -> raise Unreachable
    in
    inserts_0 @ inserts_1 @ [i_0; i_1; i_2] @ inserts, e_ret

  method private translate_valid_ptr pointer =
    let inserts_0, x' = self#translate_term pointer in
    let ret = self#fresh_pred_varinfo "valid" in
    let i_0 = Insertion.mk_decl ret in
    let dim = self#fresh_ctype_varinfo Cil.intType "valid_dim" in
    let i_1 = Insertion.mk_decl dim in
    let i_2 = self#cpc_dim (Cil.var dim) x' in
    let e2 = cmp Rgt (Cil.evar dim) zero in
    let i_3 = instru_affect (Cil.var ret) e2 in
    inserts_0 @ [i_0; i_1; i_2; i_3], (Cil.evar ret)

  method private translate_forall = self#translate_quantif ~forall:true
  method private translate_exists = self#translate_quantif ~forall:false
  method private translate_quantif ~forall logic_vars hyps goal =
    let varname = if forall then "forall" else "exists" in
    let var = self#fresh_pred_varinfo varname in
    let i_0 = Insertion.mk_decl var in
    let init_val = if forall then one else zero in
    let lvar = Cil.var var in
    let e_var = Cil.evar var in
    let i_1 = instru_affect lvar init_val in
    let negate exp = Cil.new_exp ~loc (UnOp(LNot,exp,Cil.intType)) in
    let cond = if forall then e_var else negate e_var in
    let on_lvar (i_b,e_c,i_i,i_a) lvar =
      let t1,r1,r2,t2 = Utils.extract_guards lvar hyps in
      let iter_name = lvar.lv_name in
      let i_before, e_cond, i_inside, i_after = match t1.term_type with
	| Linteger ->
	   let fresh_iter = my_Z_varinfo iter_name in
	   let i_0 = Insertion.mk_decl fresh_iter in
	   let i_1, t1' = self#translate_term t1 in
	   let i_2, t2' = self#translate_term t2 in
	   let e_iter = Cil.evar fresh_iter in
	   let i_3 = self#cinit_set e_iter t1' in
	   let inc exp = self#cbinop_ui PlusA exp exp one in
	   let i_4 = if r1 = Rlt then [inc e_iter] else [] in
	   let tmp = self#fresh_ctype_varinfo Cil.intType (varname ^ "_cmp") in
	   let i_5 = Insertion.mk_decl tmp in
	   let ltmp = Cil.var tmp in
	   let ins_b_2 = self#cbinop_ui PlusA e_iter e_iter one in
	   let e1 = cmp r2 (Cil.evar tmp) zero in
	   let i_8 = self#cclear e_iter in
	   let i_9 = self#cclear t1' in
	   let cmp, i_10 = match t2.term_type with
	     | Linteger -> self#ccmp, [ self#cclear t2' ]
	     | Lreal -> raise Unsupported
	     | _ -> self#ccmp_si, []
	   in
	   let i_6 = cmp ltmp e_iter t2' in
	   let ins_b_3 = cmp ltmp e_iter t2' in
	   let i_before = i_0 :: i_1 @ i_2 @ i_3 :: i_4 @ [i_5; i_6] in
	   let i_inside = [ins_b_2; ins_b_3] in
	   let i_after = i_8 :: i_9 :: i_10 in
	   i_before, e1, i_inside, i_after
	| Lreal -> raise Unsupported
	| _ ->
	   let iter = my_varinfo Cil.intType iter_name in
	   let insert_0 = Insertion.mk_decl iter in
	   let inserts_1, t1' = self#translate_term t1 in
	   let inserts_2, t2' = self#translate_term t2 in
	   let liter = Cil.var iter in
	   let op = match r1 with
	     | Rlt -> Cil.mkBinOp ~loc PlusA t1' one
	     | Rle -> t1'
	     | _ -> raise Unsupported
	   in
	   let e_iter = Cil.evar iter in
	   let e1 = cmp r2 e_iter t2' in
	   let e_binop = Cil.mkBinOp ~loc PlusA e_iter one in
	   let i_init = instru_affect liter op in
	   let i_before = insert_0 :: inserts_1 @ inserts_2 @ [i_init] in
	   let i_inside = [instru_affect liter e_binop] in
	   i_before, e1, i_inside, []
      in
      i_b @ i_before, Cil.mkBinOp ~loc LAnd e_cond e_c,
      i_i @ i_inside, i_a @ i_after
    in
    let i_before, e_cond, i_inside, i_after =
      List.fold_left on_lvar ([],cond,[],[]) logic_vars in
    let ins_b_0, goal_var = self#translate_predicate goal in
    let ins_b_1 = instru_affect lvar goal_var in
    let i_inside = ins_b_0 @ ins_b_1 :: i_inside in
    let i_loop = Insertion.mk_loop e_cond i_inside in
    [i_0; i_1; Insertion.mk_block (i_before @ i_loop :: i_after)], e_var

  method private translate_predicate_node p = match p with
    | Pfalse -> [], zero
    | Ptrue -> [], one
    | Prel (r,t1,t2) -> self#translate_rel r t1 t2
    | Pand (p,q) -> self#translate_and p q
    | Por (p,q) -> self#translate_or p q
    | Pimplies (p,q) -> self#translate_implies p q
    | Piff(p,q) -> self#translate_equiv p q
    | Pnot p -> self#translate_not p
    | Pif(t,p,q) -> self#translate_pif t p q
    | Pforall(vars,{pred_content=Pimplies(h,g)}) ->
       self#translate_forall vars h g
    | Pexists(vars,{pred_content=Pand(h,g)}) -> self#translate_exists vars h g
    | Pat (p, LogicLabel(_,"Here")) -> self#translate_predicate p
    | Pvalid (_,t) -> self#translate_valid t
    | Pvalid_read (_,t) ->
       Options.warning ~current:true
		       "\\valid_read(%a) is interpreted as \\valid(%a)"
		       Printer.pp_term t Printer.pp_term t;
       self#translate_valid t
    | Pforall _ ->
       Options.warning ~current:true
		       "%a not of the form \\forall ...; a ==> b"
		       Printer.pp_predicate_node p;
       raise Unsupported
    | Pexists _ ->
       Options.warning ~current:true
		       "%a not of the form \\exists ...; a && b"
		       Printer.pp_predicate_node p;
       raise Unsupported
    | Papp _
    | Pseparated _
    | Pxor _
    | Plet _
    | Pat _
    | Pinitialized _
    | Pfresh _
    | Pdangling _
    | Pallocable _
    | Pfreeable _
    | Pvalid_function _
    | Psubtype _ -> raise Unsupported

  (* modify result_varinfo when the function returns something *)
  method private compute_result_varinfo fct =
    let rec do_stmts = function
      | [] -> ()
      | {skind=Return(Some{enode=Lval(Var v,_)},_)}::_ -> result_varinfo<-Some v
      | _ :: t -> do_stmts t
    in
    do_stmts fct.sallstmts

  method private at_least_one_prop kf behaviors kloc =
    let to_prop b k = Property.ip_of_ensures kf kloc b k in
    let in_ensures b r k = r || (List.mem (to_prop b k) props) in
    let in_bhv r b = r || List.fold_left (in_ensures b) false b.b_post_cond in
    List.fold_left in_bhv false behaviors

  method private pre ~pre_entry_point kf behaviors kloc =
    let not_translated p =
      if pre_entry_point then
	let filter ret id = ret || id = p.ip_id in
	States.Not_Translated_Predicates.fold_left filter false
      else true
    in
    let translate_as_return pred =
      try
	let ins,v = self#translate_predicate (Inline.pred pred.ip_content) in
	(* untreated predicates are translated as True *)
	if not (Cil_datatype.Exp.equal v one) then
	  let e = Cil.new_exp ~loc (UnOp (LNot, v, Cil.intType)) in
	  ins @ [Insertion.mk_if e [Insertion.mk_ret zero] []]
	else ins
      with Unsupported ->
	Options.warning
	  ~current:true "%a unsupported" Printer.pp_predicate pred.ip_content;
	[]
    in
    let do_behavior ins b =
      let requires = List.filter not_translated b.b_requires in
      let typically = List.filter not_translated (Utils.typically_preds b) in
      let to_prop = Property.ip_of_requires kf kloc b in
      let in_props p = List.mem (to_prop p) props in
      let requires, typically =
	if pre_entry_point then requires, typically
	else List.filter in_props requires, List.filter in_props typically
      in
      let do_requires ins pred =
	if pre_entry_point then ins @ (translate_as_return pred)
	else
	  let prop = to_prop pred in
	  ins @ (self#pc_assert_exception pred.ip_content "" prop)
      in
      let do_typically ins pred =
	if pre_entry_point then ins @ (translate_as_return pred) else ins
      in
      if requires <> [] || typically <> [] then
	let inserts' = List.fold_left do_typically [] typically in
	let inserts = List.fold_left do_requires inserts' requires in
	if b.b_assumes <> [] then
	  let inserts_0, exp = self#cond_of_assumes b.b_assumes in
	  let insert_1 = Insertion.mk_if exp inserts [] in
	  ins @ inserts_0 @ [insert_1]
	else ins @ inserts
      else ins
    in
    List.fold_left do_behavior [] behaviors

  method private post kf behaviors kloc =
    let do_behavior ins b =
      let post = b.b_post_cond in
      let to_prop = Property.ip_of_ensures kf kloc b in
      let post = List.filter (fun x -> List.mem (to_prop x) props) post in
      let do_postcond ins (tk,pred) =
	let prop = to_prop (tk,pred) in
	ins @ (self#pc_assert_exception pred.ip_content "" prop)
      in
      if post <> [] then
	if b.b_assumes <> [] then
	  let i_0, exp = self#cond_of_assumes b.b_assumes in
	  let ii_1 = List.fold_left do_postcond [] post in
	  let i_1 = Insertion.mk_if exp ii_1 [] in
	  ins @ i_0 @ [i_1]
	else
	  let i_1 = List.fold_left do_postcond [] post in
	  ins @ i_1
      else ins
    in
    List.fold_left do_behavior [] behaviors

  (* alloc and dealloc variables for \at terms *)
  method private save_varinfo kf vi =
    let rec dig_type = function
      | TPtr (ty, _) -> Cil.stripConstLocalType ty
      | TArray (ty, _, _, _) -> Cil.stripConstLocalType ty
      | TNamed (ty, _) -> dig_type ty.ttype
      | ty ->
	 Options.feedback ~current:true "dig_type %a" Printer.pp_typ ty;
	 raise Unsupported
    in
    let rec strip_const = function
      | TPtr (t, att) -> Cil.stripConstLocalType (TPtr(strip_const t, att))
      | TArray (t,a,b,c) -> Cil.stripConstLocalType(TArray(strip_const t,a,b,c))
      | ty -> Cil.stripConstLocalType ty
    in
    let addoffset lval exp =
      let ty = Cil.typeOfLval lval in
      if Cil.isPointerType ty then
	let base = Cil.new_exp ~loc (Lval lval) in
	Mem(Cil.new_exp ~loc (BinOp(IndexPI, base, exp, ty))), NoOffset
      else if Cil.isArrayType ty then
	Cil.addOffsetLval (Index(exp, NoOffset)) lval
      else raise Unreachable
    in
    let lengths = Infer.lengths_from_requires kf in
    let terms = try Cil_datatype.Varinfo.Hashtbl.find lengths vi with _ -> [] in
    let do_varinfo v =
      let vtype = Utils.unname v.vtype in
      let my_old_v = my_varinfo (strip_const vtype) ("old_" ^ v.vname) in
      let insert_decl = Insertion.mk_decl my_old_v in
      let lmy_old_v = Cil.var my_old_v in
      let insert_before = instru_affect lmy_old_v (Cil.evar v) in
      let rec alloc_aux my_old_ptr my_ptr ty = function
	| h :: t ->
	   let ty = dig_type ty in
	   let inserts_0, h' = self#as_c_type Cil.ulongType h in
	   let my_iterator = self#fresh_ctype_varinfo Cil.ulongType "iter" in
	   let e_iterator = Cil.evar my_iterator in
	   let lmy_iterator = Cil.var my_iterator in
	   let insert_1 = Insertion.mk_decl my_iterator in
	   let e1 = Cil.new_exp ~loc (SizeOf ty) in
	   let e2 = Cil.mkBinOp ~loc Mult h' e1 in
	   let insert_2 = self#cmalloc my_old_ptr e2 in
	   let my_new_old_ptr = addoffset my_old_ptr e_iterator in
	   let my_new_ptr = addoffset my_ptr e_iterator in
	   let inserts_block = alloc_aux my_new_old_ptr my_new_ptr ty t in
	   let i_init = instru_affect lmy_iterator zero in
	   let cond = cmp Rlt e_iterator h' in
	   let e3 = Cil.mkBinOp ~loc PlusA e_iterator one in
	   let i_body = inserts_block @ [instru_affect lmy_iterator e3] in
	   let insert_3 = Insertion.mk_loop cond i_body in
	   inserts_0 @ [insert_1 ; insert_2; i_init; insert_3]
	| [] -> [instru_affect my_old_ptr (Cil.new_exp ~loc (Lval my_ptr))]
      in
      if Cil.isPointerType vtype || Cil.isArrayType vtype then
	let my_old_ptr = my_varinfo (strip_const vtype) ("old_ptr_"^v.vname)in
	let insert_0 = Insertion.mk_decl my_old_ptr in
	let inserts_decl = [insert_decl; insert_0] in
	let ins = alloc_aux (Cil.var my_old_ptr) (Cil.var v) vtype terms in
	let inserts_before = insert_before :: ins in
	inserts_decl, inserts_before
      else [insert_decl], [insert_before]
    in
    let inserts_decl, inserts_before = do_varinfo vi in
    let do_varinfo v =
      let vtype = Utils.unname v.vtype in
      let rec dealloc_aux my_old_ptr = function
	| [] -> []
	| _ :: [] -> [ self#cfree(Cil.new_exp ~loc (Lval my_old_ptr)) ]
	| h :: t ->
	   let my_iterator = self#fresh_ctype_varinfo Cil.ulongType "iter" in
	   let e_iterator = Cil.evar my_iterator in
	   let lmy_iterator = Cil.var my_iterator in
	   let insert_0 = Insertion.mk_decl my_iterator in
	   let inserts_1, h' = self#as_c_type Cil.ulongType h in
	   let aux = addoffset my_old_ptr (Cil.evar my_iterator) in
	   let inserts_block = dealloc_aux aux t in
	   let cond = cmp Rlt e_iterator h' in
	   let e1 = Cil.mkBinOp ~loc PlusA e_iterator one in
	   let e = Cil.new_exp ~loc (Lval my_old_ptr) in
	   let i_body = inserts_block @ [instru_affect lmy_iterator e1] in
	   let i_loop = Insertion.mk_loop cond i_body in
	   let i_init = instru_affect lmy_iterator zero in
	   let i_free = self#cfree e in
	   insert_0 :: inserts_1 @ [i_init; i_loop ; i_free]
      in
      if Cil.isPointerType vtype || Cil.isArrayType vtype then
	let my_old_ptr = my_varinfo vtype ("old_ptr_" ^ v.vname) in
	dealloc_aux (Cil.var my_old_ptr) terms
      else []
    in
    let inserts_after = do_varinfo vi in
    inserts_decl, inserts_before, inserts_after

  method! vfunc f =
    let entry_point = Kernel_function.get_name (fst(Globals.entry_point())) in
    let kf = Globals.Functions.find_by_name f.svar.vname in
    let behaviors = Annotations.behaviors kf in
    self#compute_result_varinfo f;
    let pre_entry_point = f.svar.vname = entry_point in
    let fprename = f.svar.vname ^ "_precond" in
    let fname = if pre_entry_point then fprename else f.svar.vname in
    let label_pre = Symbolic_label.beg_func fname in
    let inserts_pre = self#pre ~pre_entry_point kf behaviors Kglobal in
    List.iter (self#insert label_pre) inserts_pre;
    if self#at_least_one_prop kf behaviors Kglobal then
      begin
	let inserts = self#post kf behaviors Kglobal in
	let label = Symbolic_label.end_func f.svar.vname in
	self#insert label (Insertion.mk_block inserts)
      end;
    let do_varinfo v =
      let inserts_decl,inserts_before,inserts_after = self#save_varinfo kf v in
      let beg_label = Symbolic_label.beg_func f.svar.vname
      and end_label = Symbolic_label.end_func f.svar.vname in
      List.iter (self#insert beg_label) inserts_decl;
      List.iter (self#insert beg_label) inserts_before;
      List.iter (self#insert end_label) inserts_after
    in
    List.iter do_varinfo visited_globals;
    List.iter do_varinfo (Kernel_function.get_formals kf);
    Cil.DoChildren

  method private cond_of_assumes pred_list =
    let rec aux insertions ret = function
      | [] -> insertions, ret
      | h :: t ->
	 let ins,v = self#translate_predicate (Inline.pred h.ip_content) in
	 let e = Cil.mkBinOp ~loc LAnd ret v in
	 aux (insertions @ ins) e t
    in
    aux [] one pred_list

  method private cond_of_behaviors pred_lists =
    let rec aux insertions ret = function
      | [] -> insertions, ret
      | h :: t ->
	 let ins, v = self#cond_of_assumes h in
	 let e = Cil.mkBinOp ~loc LOr ret v in
	 aux (insertions @ ins) e t
    in
    aux [] zero pred_lists

  method private pc_exc str i =
    let rec aux ret = function
      | [] -> ret
      | [h] -> aux (ret ^ (string_of_int h)) []
      | h :: t -> aux (ret ^ (string_of_int h) ^ ",") t
    in
    let swd_str = match swd with
      | [] -> ""
      | x -> Format.sprintf "%s$" (aux "" x)
    in
    let str = Cil.mkString ~loc (swd_str ^ str) in
    let const = CInt64(Integer.of_int i, IInt, Some(string_of_int i)) in
    self#cpc_exc str (Cil.new_exp ~loc (Const const))

  method private pc_ass str i =
    let str = Cil.mkString ~loc str in
    let const = CInt64(Integer.of_int i, IInt, Some(string_of_int i)) in
    self#cpc_assume str (Cil.new_exp ~loc (Const const))

  method private pc_to_fc str = self#cpc_to_fc (Cil.mkString ~loc str)

  method private pc_assert_exception pred msg prop =
    try
      let inserts_0, var = self#translate_predicate (Inline.pred pred) in
      let e = Cil.new_exp ~loc (UnOp(LNot, var, Cil.intType)) in
      let id = Utils.to_id prop in
      let insert_1 = Insertion.mk_if e [ self#pc_exc msg id ] [] in
      translated_properties <- prop :: translated_properties;
      inserts_0 @ [insert_1]
    with Unsupported ->
      Options.warning
	~current:true "%a unsupported" Printer.pp_predicate pred;
      []

  method private pc_assume pred =
    try
      let inserts_0, var = self#translate_predicate (Inline.pred pred) in
      let e = Cil.new_exp ~loc (UnOp(LNot, var, Cil.intType)) in
      inserts_0 @ [ Insertion.mk_if e [ self#pc_ass "" 0 ] [] ]
    with Unsupported ->
      Options.warning
	~current:true "%a unsupported" Printer.pp_predicate pred;
      []

  method private for_behaviors bhvs ins = match bhvs with
  | [] -> ins
  | bhvs ->
     let inserts_0, cond = self#cond_of_behaviors bhvs in
     inserts_0 @ [ Insertion.mk_if cond ins [] ]

  method private translate_stmt_spec kf stmt bhvs spec =
    if self#at_least_one_prop kf spec.spec_behavior (Kstmt stmt) then
      begin
	let stmt_bhvs = spec.spec_behavior in
	let ins = self#pre ~pre_entry_point:false kf stmt_bhvs (Kstmt stmt) in
	let ins = self#for_behaviors bhvs ins in
	List.iter (self#insert (Symbolic_label.beg_stmt stmt.sid)) ins;
	let ins = self#post kf stmt_bhvs (Kstmt stmt) in
	let ins = if bhvs = [] then ins else self#for_behaviors bhvs ins in
	List.iter (self#insert (Symbolic_label.end_stmt stmt.sid)) ins;
      end

  method private translate_assert kf stmt ca for_behaviors pred =
    let prop = Property.ip_of_code_annot_single kf stmt ca in
    if List.mem prop props then
      let ins = self#pc_assert_exception pred "" prop in
      let inserts = self#for_behaviors for_behaviors ins in
      List.iter (self#insert (Symbolic_label.beg_stmt stmt.sid)) inserts

  method private translate_invariant kf stmt ca for_behaviors pred =
    let prop = Property.ip_of_code_annot_single kf stmt ca in
    if List.mem prop props then
      let f label msg =
	let ins = self#pc_assert_exception pred msg prop in
	let inserts = self#for_behaviors for_behaviors ins in
	List.iter (self#insert label) inserts
      in
      f (Symbolic_label.beg_stmt stmt.sid) "not established";
      f (Symbolic_label.end_iter stmt.sid) "not preserved"

  method private translate_variant kf stmt ca term =
    let prop = Property.ip_of_code_annot_single kf stmt ca in
    translated_properties <- prop :: translated_properties;
    if List.mem prop props then
      let id = Utils.to_id prop in
      let beg_label = Symbolic_label.beg_iter stmt.sid
      and end_label = Symbolic_label.end_iter stmt.sid in
      match term.term_type with
      | Linteger ->
	 (* at BegIter *)
	 let inserts_1, beg_variant = self#translate_term term in
	 List.iter (self#insert beg_label) inserts_1;
	 let cmp_variant_zero =
	   self#fresh_ctype_varinfo Cil.intType "variant_pos" in
	 let e_cmp_variant_zero = Cil.evar cmp_variant_zero in
	 let l_cmp_variant_zero = Cil.var cmp_variant_zero in
	 let instr = self#pc_exc "non positive" id in
	 self#insert beg_label (Insertion.mk_decl cmp_variant_zero);
	 let i_2 = self#ccmp_ui l_cmp_variant_zero beg_variant zero in
	 self#insert beg_label i_2;
	 let cond = cmp Rlt e_cmp_variant_zero zero in
	 self#insert beg_label (Insertion.mk_if cond [instr] []);
	 (* at EndIter *)
	 let inserts_4, end_variant = self#translate_term term in
	 List.iter (self#insert end_label) inserts_4;
	 let cmp_variants =
	   self#fresh_ctype_varinfo Cil.intType "variant_decr" in
	 let e_cmp_variants = Cil.evar cmp_variants in
	 let l_cmp_variants = Cil.var cmp_variants in
	 let instr = self#pc_exc "non decreasing" id in
	 self#insert end_label (Insertion.mk_decl cmp_variants);
	 let i_4 = self#ccmp l_cmp_variants end_variant beg_variant in
	 self#insert end_label i_4;
	 let cond = cmp Rge e_cmp_variants zero in
	 self#insert end_label (Insertion.mk_if cond [instr] []);
	 self#insert end_label (self#cclear beg_variant)
      | Lreal -> raise Unsupported
      | _ ->
	 (* at BegIter *)
	 let inserts_1, beg_variant = self#translate_term term in
	 List.iter (self#insert beg_label) inserts_1;
	 let cond = cmp Rlt beg_variant zero in
	 let instr = self#pc_exc "non positive" id in
	 self#insert beg_label (Insertion.mk_if cond [instr] []);
	 let save_variant =
	   self#fresh_ctype_varinfo Cil.intType "variant_save" in
	 let l_save_variant = Cil.var save_variant in
	 let e_save_variant = Cil.evar save_variant in
	 self#insert beg_label (Insertion.mk_decl save_variant);
	 let insert = instru_affect l_save_variant beg_variant in
	 self#insert beg_label insert;
	 (* at EndIter *)
	 let inserts_2, end_variant = self#translate_term term in
	 List.iter (self#insert end_label) inserts_2;
	 let cond = cmp Rge end_variant e_save_variant in
	 let instr = self#pc_exc "non decreasing" id in
	 self#insert end_label (Insertion.mk_if cond [instr] [])

  method! vcode_annot ca =
    let stmt = Extlib.the self#current_stmt in
    let kf = Kernel_function.find_englobing_kf stmt in
    let bhv_names = match ca.annot_content with
      | AAssert (b,_) | AStmtSpec (b,_) | AInvariant (b,_,_) -> b | _ -> []
    in
    let on_behavior s _ b ret = if b.b_name = s then b.b_assumes else ret in
    let on_behavior_name s = Annotations.fold_behaviors (on_behavior s) kf [] in
    let bhvs = List.map on_behavior_name bhv_names in
    begin
      match ca.annot_content with
      | AStmtSpec(_,spec) -> self#translate_stmt_spec kf stmt bhvs spec
      | AAssert(_,pred) -> self#translate_assert kf stmt ca bhvs pred
      | AInvariant(_,true,pred) -> self#translate_invariant kf stmt ca bhvs pred
      | AVariant(term,_) -> self#translate_variant kf stmt ca term
      | _ -> ()
    end;
    Cil.DoChildren

  method private assigns_swd assigns =
    let assigns_terms =
      match List.fold_left Logic_utils.merge_assigns WritesAny assigns with
      | WritesAny ->
	 Options.warning
	   ~current:true ~once:true "assigns clause not precise enough";
	 []
      | Writes terms -> List.map fst terms
    in
    let on_term ret term =
      let t = term.it_content in
      match t.term_node with
      | TLval(TMem{term_node=TBinOp(op, op1,
				    {term_node=Trange (Some t1, Some t2)})},
	      TNoOffset) ->
	 let ty =
	   match op1.term_type with Ctype t -> t | _ -> raise Unreachable in
	 let it = self#fresh_ctype_varinfo Cil.intType "iter" in
	 let e_it = Cil.evar it
	 and l_it = Cil.var it in
	 let i_0 = Insertion.mk_decl it in
	 let i_1, e_t1 = self#as_c_type Cil.intType t1 in
	 let i_2 = instru_affect l_it e_t1 in
	 let i_3, e_t2 = self#as_c_type Cil.intType t2 in
	 let cond = cmp Rle e_it e_t2 in
	 let ll, e_op1 = self#translate_term op1 in
	 assert (ll = []);
	 let e = Cil.new_exp ~loc (BinOp(op, e_op1, e_it, ty)) in
	 let y = Mem e, NoOffset in
	 let i_f_1 = self#cnondet (Cil.typeOfLval y) y in
	 let plus_one = Cil.mkBinOp ~loc PlusA e_it one in
	 let i_f_2 = instru_affect l_it plus_one in
	 let i_7 = Insertion.mk_loop cond [i_f_1; i_f_2] in
	 i_0::i_1 @ i_2::i_3 @ i_7::ret
      | TLval lv ->
	 let ty = match t.term_type with Ctype x -> x | _-> raise Unreachable in
	 let ins, e = self#translate_lval lv in
	 let aff = self#cnondet ty e in
	 ins @ aff :: ret
      | _ ->
	 Options.warning
	   ~current:true "term %a in assigns clause unsupported"
	   Printer.pp_term t;
	 ret
    in
    List.fold_left on_term [] assigns_terms

  method! vstmt_aux stmt =
    let sim_funcs = Options.Simulate_Functions.get() in
    match stmt.skind with
    | Loop _ when List.mem stmt.sid swd ->
       let kf = Kernel_function.find_englobing_kf stmt in
       let ca_l = Annotations.code_annot stmt in
       let ca_l = List.map (fun x -> x.annot_content) ca_l in
       let on_bhv _ bhv ins =
	 let bhv_in l =
	   List.mem bhv.b_name l || (Cil.is_default_behavior bhv && l = []) in
	 let f_assigns ret = function
	   | AAssigns (l, a) when bhv_in l -> a :: ret
	   | _ -> ret
	 in
	 let f_linvs ret = function
	   | AInvariant(l, _, p) when bhv_in l -> p :: ret
	   | _ -> ret
	 in
	 let assigns = List.fold_left f_assigns [] ca_l in
	 let linvs = List.fold_left f_linvs [] ca_l in
	 let ins_assumes, e_assumes = self#cond_of_assumes bhv.b_assumes in
	 let affects = self#assigns_swd assigns in
	 let on_inv ret p = ret @ (self#pc_assume p) in
	 let ins_block = List.fold_left on_inv affects linvs in
	 let ins_bhv = Insertion.mk_if e_assumes ins_block [] in
	 ins @ ins_assumes @ [ins_bhv]
       in
       let ins_h = Annotations.fold_behaviors on_bhv kf [] in
       Cil.DoChildrenPost (fun s ->
	 List.iter (self#insert (Symbolic_label.beg_stmt stmt.sid)) ins_h; s)
	 
    | Instr (Call(ret,{enode=Lval(Var fct_varinfo,NoOffset)},args,_))
	 when List.mem stmt.sid swd || List.mem fct_varinfo.vname sim_funcs ->
       let kf = Globals.Functions.get fct_varinfo in
       let formals = Kernel_function.get_formals kf in
       let locals = [] in
       let varname = fct_varinfo.vname ^ "_mod" in
       let new_f_vi = self#fresh_fct_varinfo fct_varinfo.vtype varname in
       let on_bhv _ bhv ins =
	 let ins_assumes, e_assumes = self#cond_of_assumes bhv.b_assumes in
	 (* we create variables old_* to save the values of globals and
	  * formal parameters before function call *)
	 let save v (a,b,c) = let d,e,f=self#save_varinfo kf v in d@a,e@b,f@c in
	 let save_global v _ l = save v l in
	 let save_formal l v = save v l in
	 let i1,i2,i3 = Globals.Vars.fold_in_file_order save_global ([],[],[])in
	 let i1,i2,i3 = List.fold_left save_formal (i1,i2,i3) formals in
	 let begin_save = i1 @ i2 and end_save = i3 in
	 let ensures = bhv.b_post_cond in
	 let on_post ins (_,{ip_content=p}) =
	   let p = match ret with
	     | Some r ->
		let ty = Cil.typeOfLval r in
		result_varinfo <- Some (my_varinfo ty "__retres");
		Inline.pred p
	     | None -> p
	   in
	   ins @ (self#pc_assume p)
	 in
	 let posts = List.fold_left on_post [] ensures in
	 let affects = self#assigns_swd [bhv.b_assigns] in
	 let i_then = begin_save @ affects @ posts @ end_save in
	 let ins_bhv = Insertion.mk_if e_assumes i_then [] in
	 ins @ ins_assumes @ [ins_bhv]
       in
       let ins_body = Annotations.fold_behaviors on_bhv kf [] in
       let decl_retres, aff_retres, ret_retres = match ret with
	 | Some r ->
	    let ty = Cil.typeOfLval r in
	    let retres = my_varinfo ty "__retres" in
	    let e_retres = Cil.evar retres in
	    let aff = self#cnondet ty (Cil.var retres) in
	    [Insertion.mk_decl retres], [aff], [Insertion.mk_ret e_retres]
	 | None -> [], [], []
       in
       let ins_full_body = decl_retres @ aff_retres @ ins_body @ ret_retres in
       let new_f = Function.make new_f_vi formals locals ins_full_body in
       functions <- new_f :: functions;
       let i_call = Insertion.mk_instru(Call(ret,Cil.evar new_f_vi,args,loc)) in
       self#insert (Symbolic_label.end_stmt stmt.sid) i_call;
       Cil.SkipChildren
    | _ -> Cil.DoChildren

  method! vglob_aux = function
    | GVar(vi,_,_) -> visited_globals <- vi::visited_globals; Cil.DoChildren
    | _ -> Cil.DoChildren
end


let translate props swd precond_fname instru_fname =
  let constraints = Input_domain.compute_constraints() in
  let gatherer = new gather_insertions props swd in
  Visitor.visitFramacFile (gatherer :> Visitor.frama_c_inplace) (Ast.get());
  let insertions = gatherer#get_insertions()
  and functions = gatherer#get_functions()
  and translated_props = gatherer#translated_properties()
  and new_globals = gatherer#get_new_globals()
  and new_init_globals = gatherer#get_new_init_globals() in
  let print_insertions_at_label lab insertions =
    let dkey = Options.dkey_insertions in
    let f ins =
      Options.feedback
	~dkey "/* %a */ %a" Symbolic_label.pretty lab
	(Insertion.pretty ~line_break:true) ins
    in
    Queue.iter f insertions;
    Options.feedback ~dkey "--------------------"
  in
  Hashtbl.iter print_insertions_at_label insertions;
  let add_global = Input_domain.add_global in
  let add_init_global = Input_domain.add_init_global in 
  let constraints = List.fold_left add_global constraints new_globals in
  let constraints =
    List.fold_left add_init_global constraints new_init_globals in
  Input_domain.translate precond_fname constraints;
  let old_unicode = Kernel.Unicode.get() in
  Kernel.Unicode.set false;
  let printer = new Print.print_insertions insertions functions swd in
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  printer#file fmt (Ast.get());
  let dkey = Options.dkey_generated_c in
  let out_file = open_out instru_fname in
  Options.debug ~dkey "generated C file:";
  let dkeys = Options.Debug_category.get() in
  if Datatype.String.Set.mem "generated-c" dkeys then
    Buffer.output_buffer stdout buf;
  Buffer.output_buffer out_file buf;
  Format.pp_print_flush fmt();
  flush stdout;
  flush out_file;
  close_out out_file;
  Buffer.clear buf;
  Kernel.Unicode.set old_unicode;
  translated_props
