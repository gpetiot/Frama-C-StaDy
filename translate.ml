open Cil_types

exception Unreachable

exception Unsupported

let loc = Cil_datatype.Location.unknown

(* varinfos *)
let my_varinfo ty varname = Cil.makeVarinfo false false varname ty

let my_Z_varinfo s = my_varinfo (Utils.mpz_t ()) s

(* expressions *)
let zero = Cil.zero ~loc

let one = Cil.one ~loc

let cmp rel e1 e2 = Cil.mkBinOp ~loc (Utils.relation_to_binop rel) e1 e2

let mk_affect a b = Cil.mkStmt (Instr (Set (a, b, loc)))

let mk_ret e = Cil.mkStmt (Return (Some e, loc))

class gather_insertions props swd =
  object (self)
    inherit Visitor.frama_c_inplace

    val insertions = Hashtbl.create 64

    val mutable functions : Cil_types.fundec list = []

    val mutable result_varinfo = None

    val mutable in_old_term = false

    val mutable in_old_ptr = false

    val mutable visited_globals = []

    val last_varname = Datatype.String.Hashtbl.create 64

    val mutable translated_properties = []

    val mutable fcts_called : varinfo list = []

    method get_insertions () = insertions

    method get_functions () = functions

    method private call fct ret args =
      let vi = States.Externals.find fct in
      self#add_function_call vi ;
      Cil.mkStmt (Instr (Call (ret, Cil.evar vi, args, loc)))

    method cmalloc x y = self#call "malloc" (Some x) [y]

    method cfree x = self#call "free" None [x]

    method cpc_dim x y = self#call "pathcrawler_dimension" (Some x) [y]

    method cpc_exc x y = self#call "pathcrawler_assert_exception" None [x; y]

    method cpc_assume x y = self#call "pathcrawler_assume_exception" None [x; y]

    method cpc_to_fc x = self#call "pathcrawler_to_framac" None [x]

    method cclear x = self#call "__gmpz_clear" None [x]

    method cinit x = self#call "__gmpz_init" None [x]

    method cinit_set x y = self#call "__gmpz_init_set" None [x; y]

    method cinit_set_ui x y = self#call "__gmpz_init_set_ui" None [x; y]

    method cinit_set_si x y = self#call "__gmpz_init_set_si" None [x; y]

    method cinit_set_str x y z = self#call "__gmpz_init_set_str" None [x; y; z]

    method cset x y = self#call "__gmpz_set" None [x; y]

    method cabs x y = self#call "__gmpz_abs" None [x; y]

    method cadd x y z = self#call "__gmpz_add" None [x; y; z]

    method cadd_ui x y z = self#call "__gmpz_add_ui" None [x; y; z]

    method csub x y z = self#call "__gmpz_sub" None [x; y; z]

    method csub_ui x y z = self#call "__gmpz_sub_ui" None [x; y; z]

    method cui_sub x y z = self#call "__gmpz_ui_sub" None [x; y; z]

    method cmul x y z = self#call "__gmpz_mul" None [x; y; z]

    method cmul_ui x y z = self#call "__gmpz_mul_ui" None [x; y; z]

    method cmul_si x y z = self#call "__gmpz_mul_si" None [x; y; z]

    method ctdiv_q x y z = self#call "__gmpz_tdiv_q" None [x; y; z]

    method ctdiv_q_ui x y z = self#call "__gmpz_tdiv_q_ui" None [x; y; z]

    method ctdiv_r x y z = self#call "__gmpz_tdiv_r" None [x; y; z]

    method ctdiv_r_ui x y z = self#call "__gmpz_tdiv_r_ui" None [x; y; z]

    method cbinop op x y z =
      self#call ("__gmpz_" ^ Utils.binop_to_fname op) None [x; y; z]

    method cbinop_ui op x y z =
      self#call ("__gmpz_" ^ Utils.binop_to_fname op ^ "_ui") None [x; y; z]

    method cget_ui x y = self#call "__gmpz_get_ui" (Some x) [y]

    method cget_si x y = self#call "__gmpz_get_si" (Some x) [y]

    method ccmp x y z = self#call "__gmpz_cmp" (Some x) [y; z]

    method ccmp_ui x y z = self#call "__gmpz_cmp_ui" (Some x) [y; z]

    method ccmp_si x y z = self#call "__gmpz_cmp_si" (Some x) [y; z]

    method cmul_2exp x y z = self#call "__gmpz_mul_2exp" None [x; y; z]

    method cfdiv_q_2exp x y z = self#call "__gmpz_fdiv_q_2exp" None [x; y; z]

    method cnondet ty x y =
      self#call ("nondet_" ^ Utils.typename ty) (Some x) [y]

    method private add_function_call vi =
      if List.mem vi fcts_called then () else fcts_called <- vi :: fcts_called

    method get_new_globals () =
      let on_varinfo ret v =
        try
          (* the nondet values (as an array) of each type *)
          if String.sub v.vname 0 7 = "nondet_" then
            let vname1 = v.vname ^ "_val" in
            let ty1 = TPtr (Cil.getReturnType v.vtype, []) in
            let vi1 = Cil.makeVarinfo false false vname1 ty1 in
            vi1 :: ret
          else ret
        with _ -> ret
      in
      List.fold_left on_varinfo [] fcts_called

    (* those globals are initialized to zero *)
    method get_new_init_globals () =
      let on_varinfo ret v =
        try
          (* the number of nondet values of each type *)
          if String.sub v.vname 0 7 = "nondet_" then
            let vname2 = v.vname ^ "_cpt" in
            let vi2 = Cil.makeVarinfo false false vname2 Cil.uintType in
            vi2 :: ret
          else ret
        with _ -> ret
      in
      List.fold_left on_varinfo [] fcts_called

    method private insert label e =
      let add q x = Queue.add x q in
      try
        let v, s, c = Hashtbl.find insertions label in
        List.iter (add v) (Env.locals e) ;
        List.iter (add s) (Env.stmts e) ;
        List.iter (add c) (Env.cleans e)
      with Not_found ->
        let v = Queue.create () in
        let s = Queue.create () in
        let c = Queue.create () in
        List.iter (add v) (Env.locals e) ;
        List.iter (add s) (Env.stmts e) ;
        List.iter (add c) (Env.cleans e) ;
        Hashtbl.add insertions label (v, s, c)

    method private fresh_varinfo ty varname =
      let varname = "__sd_" ^ varname in
      let i =
        try Datatype.String.Hashtbl.find last_varname varname + 1
        with Not_found -> 0
      in
      Datatype.String.Hashtbl.replace last_varname varname i ;
      my_varinfo ty (varname ^ "_" ^ string_of_int i)

    method private fresh_Z_varinfo varname =
      self#fresh_varinfo (Utils.mpz_t ()) ("Z_" ^ varname)

    method private fresh_bool_varinfo vname =
      self#fresh_varinfo Cil.intType vname

    method translated_properties () = translated_properties

    method private translate_constant ty =
      function
      | Integer (i, str_opt) -> (
        match ty with
        | Linteger ->
            let fresh_var = self#fresh_Z_varinfo "cst" in
            let str = try Extlib.the str_opt with _ -> Integer.to_string i in
            let str = Cil.mkString ~loc str in
            let ten = CInt64 (Integer.of_int 10, Cil_types.IInt, Some "10") in
            let e_ten = Cil.new_exp ~loc (Const ten) in
            let i_1 = self#cinit_set_str (Cil.evar fresh_var) str e_ten in
            let i_2 = self#cclear (Cil.evar fresh_var) in
            (Env.make [fresh_var] [i_1] [i_2], Lval (Var fresh_var, NoOffset))
        | Ctype (TInt (ik, _)) -> (Env.empty, Const (CInt64 (i, ik, str_opt)))
        | _ -> raise Unreachable )
      | LStr str -> (Env.empty, Const (CStr str))
      | LWStr i64_l -> (Env.empty, Const (CWStr i64_l))
      | LChr c -> (Env.empty, Const (CChr c))
      | LReal {r_literal= s; r_nearest= f; r_lower= l; r_upper= u} ->
          if l <> u then
            Options.warning ~current:true ~once:true
              "approximating a real number by a float" ;
          (Env.empty, Const (CReal (f, FLongDouble, Some s)))
      | LEnum e -> (Env.empty, Const (CEnum e))

    method private translate_var lv =
      let varname =
        match self#current_func with
        | Some _ when in_old_term -> (
          match (lv.lv_origin, lv.lv_type) with
          | Some _, Ctype ty
            when (Cil.isPointerType ty || Cil.isArrayType ty) && in_old_ptr ->
              "old_ptr_" ^ lv.lv_name
          | Some _, _ -> "old_" ^ lv.lv_name
          | None, _ -> lv.lv_name )
        | _ -> lv.lv_name
      in
      match lv.lv_type with
      | Linteger -> my_Z_varinfo varname
      | Lreal -> raise Unsupported
      | Ctype ty -> my_varinfo ty varname
      | _ -> raise Unreachable

    method private translate_unop op t =
      match op with
      | Neg -> (
        match t.term_type with
        | Linteger | Ctype _ ->
            let env1, x = self#as_logic_type Linteger (Cil.lzero ()) in
            let env2, y = self#as_logic_type Linteger t in
            let ret = self#fresh_Z_varinfo "neg" in
            let i_1 = self#cinit (Cil.evar ret) in
            let i_2 = self#cbinop MinusA (Cil.evar ret) x y in
            let i_3 = self#cclear (Cil.evar ret) in
            ( Env.merge env1 (Env.merge env2 (Env.make [ret] [i_1; i_2] [i_3]))
            , (Cil.evar ret).enode )
        | _ -> raise Unsupported )
      | _ -> raise Unsupported

    method private translate_shift ty varname shift a b =
      match ty with
      | Linteger ->
          let env1, x = self#as_logic_type Linteger a in
          let env2, y = self#as_c_type Cil.ulongLongType b in
          let v = self#fresh_Z_varinfo varname in
          let i1 = self#cinit (Cil.evar v) in
          let i2 = shift (Cil.evar v) x y in
          let i3 = self#cclear (Cil.evar v) in
          ( Env.merge env1 (Env.merge env2 (Env.make [v] [i1; i2] [i3]))
          , (Cil.evar v).enode )
      | _ -> raise Unreachable

    method private translate_binop ty op a b =
      match op with
      | IndexPI | PlusPI | MinusPI ->
          let env1, a' = self#translate_term a in
          let env2, b' = self#as_c_type Cil.intType b in
          (Env.merge env1 env2, BinOp (op, a', b', Cil.typeOf a'))
      | Shiftlt -> self#translate_shift ty "lshift" self#cmul_2exp a b
      | Shiftrt -> self#translate_shift ty "rshift" self#cfdiv_q_2exp a b
      | _ -> (
        match ty with
        | Linteger ->
            let env1, x = self#as_logic_type Linteger a in
            let env2, y = self#as_logic_type Linteger b in
            let v = self#fresh_Z_varinfo (Utils.binop_to_fname op) in
            let i1 = self#cinit (Cil.evar v) in
            let i2 = self#cbinop op (Cil.evar v) x y in
            let i3 = self#cclear (Cil.evar v) in
            ( Env.merge env1 (Env.merge env2 (Env.make [v] [i1; i2] [i3]))
            , (Cil.evar v).enode )
        | Lreal -> raise Unsupported
        | Ltype _ as lt when Logic_const.is_boolean_type lt ->
            let env1, x = self#translate_term a in
            let env2, y = self#translate_term b in
            let env3, e =
              match (a.term_type, b.term_type) with
              | Linteger, Linteger ->
                  let var = self#fresh_varinfo Cil.intType "binop" in
                  let tmp = self#fresh_bool_varinfo "binop_cmp" in
                  let i_1 = self#ccmp (Cil.var tmp) x y in
                  let op = Utils.binop_to_relation op in
                  let i_2 =
                    mk_affect (Cil.var var) (cmp op (Cil.evar tmp) zero)
                  in
                  (Env.make [var; tmp] [i_1; i_2] [], Cil.evar var)
              | _ -> (Env.empty, Cil.mkBinOp ~loc op x y)
            in
            (Env.merge env1 (Env.merge env2 env3), e.enode)
        | _ -> raise Unreachable )

    method private translate_tif cond then_b else_b =
      match then_b.term_type with
      | Linteger ->
          let ret = self#fresh_Z_varinfo "tif" in
          let i_1 = self#cinit (Cil.evar ret) in
          let env, cond' = self#translate_term cond in
          let tmp = self#fresh_bool_varinfo "tif_cmp" in
          let i_2 = self#ccmp_si (Cil.var tmp) cond' zero in
          let env1, then_b' = self#translate_term then_b in
          let set_1 = self#cset (Cil.evar ret) then_b' in
          let i_then = Env.merge env1 (Env.make [] [set_1] []) in
          let env2, else_b' = self#translate_term else_b in
          let set_2 = self#cset (Cil.evar ret) else_b' in
          let i_else = Env.merge env2 (Env.make [] [set_2] []) in
          let i_3 = Env.mk_if (cmp Rneq (Cil.evar tmp) zero) i_then i_else in
          let i_4 = self#cclear (Cil.evar ret) in
          ( Env.merge env (Env.make [ret; tmp] [i_1; i_2; i_3] [i_4])
          , (Cil.evar ret).enode )
      | Lreal -> raise Unsupported
      | _ -> raise Unreachable

    method private translate_at t =
      function
      | BuiltinLabel (Old | Pre) ->
          let is_ptr =
            match t.term_node with TLval (TMem _, _) -> true | _ -> false
          in
          if is_ptr then in_old_ptr <- true ;
          in_old_term <- true ;
          let env, v = self#translate_term t in
          if is_ptr then in_old_ptr <- false ;
          in_old_term <- false ;
          (env, v.enode)
      | BuiltinLabel (Post | Here) ->
          (* label Post is only encoutered in post-conditions, and \at(t,Post)
      * in a post-condition is t *)
          let env, v = self#translate_term t in
          (env, v.enode)
      | _ -> raise Unsupported

    (* C type -> logic type *)
    method private translate_logic_coerce lt t =
      match lt with
      | Linteger ->
          let ty =
            match t.term_type with
            | Ctype x -> Ctype (Cil.unrollType x)
            | x -> x
          in
          let env, v = self#translate_term t in
          let ret = self#fresh_Z_varinfo "to_Z" in
          let init_set =
            match ty with
            | Ctype x ->
                if Cil.isUnsignedInteger x then self#cinit_set_ui
                else self#cinit_set_si
            | _ -> raise Unsupported
          in
          let i_1 = init_set (Cil.evar ret) v in
          let i_2 = self#cclear (Cil.evar ret) in
          (Env.merge env (Env.make [ret] [i_1] [i_2]), (Cil.evar ret).enode)
      | Lreal -> raise Unsupported
      | _ -> raise Unreachable

    (* logic type -> C type *)
    method private translate_coerce t ty =
      match t.term_type with
      | Linteger ->
          let env, v = self#translate_term t in
          let ret = self#fresh_varinfo ty "to_ctype" in
          let get =
            if Cil.isUnsignedInteger ty then self#cget_ui else self#cget_si
          in
          let i_1 = get (Cil.var ret) v in
          (Env.merge env (Env.make [ret] [i_1] []), (Cil.evar ret).enode)
      | Lreal -> raise Unsupported
      | _ -> raise Unreachable

    method private as_logic_type ty t =
      if ty = t.term_type then self#translate_term t
      else
        let i, e = self#translate_logic_coerce ty t in
        (i, Cil.new_exp ~loc e)

    method private as_c_type ty t =
      if Ctype ty = t.term_type then self#translate_term t
      else
        let i, e = self#translate_coerce t ty in
        (i, Cil.new_exp ~loc e)

    method private translate_lambda lower upper q t init vname compute =
      assert (lower.term_type = Linteger && upper.term_type = Linteger) ;
      let ret = self#fresh_Z_varinfo vname in
      let i_1 = self#cinit_set_si (Cil.evar ret) init in
      let i_2 = self#cclear (Cil.evar ret) in
      let block_env =
        let env1, low = self#translate_term lower in
        let env2, up = self#translate_term upper in
        let iter = my_Z_varinfo q.lv_name in
        let tmp = self#fresh_bool_varinfo (vname ^ "_cmp") in
        let i1 = self#cinit_set (Cil.evar iter) low in
        let i2 = self#ccmp (Cil.var tmp) (Cil.evar iter) up in
        let loop_env =
          let env, lambda_t = self#translate_term t in
          let i_1 = self#cbinop_ui PlusA (Cil.evar iter) (Cil.evar iter) one in
          let i_2 = self#ccmp (Cil.var tmp) (Cil.evar iter) up in
          let i_3 = compute (Cil.evar ret) lambda_t in
          Env.merge env (Env.make [] [i_1; i_2; i_3] [])
        in
        let i3 = Env.mk_loop (cmp Rle (Cil.evar tmp) zero) loop_env in
        let i4 = self#cclear (Cil.evar iter) in
        Env.merge env1
          (Env.merge env2 (Env.make [iter; tmp] [i1; i2; i3] [i4]))
      in
      (Env.make [ret] [i_1; Env.mk_block block_env] [i_2], (Cil.evar ret).enode)

    method private translate_app li ll params =
      let do_op op r l = self#cbinop op r r l in
      let fname = li.l_var_info.lv_name in
      match (Extlib.the li.l_type, params, fname) with
      | Linteger, [param], "\\abs" ->
          let env, x = self#translate_term param in
          let ret = self#fresh_Z_varinfo "abs" in
          let i_1 = self#cinit (Cil.evar ret) in
          let i_2 = self#cabs (Cil.evar ret) x in
          let i_3 = self#cclear (Cil.evar ret) in
          ( Env.merge env (Env.make [ret] [i_1; i_2] [i_3])
          , (Cil.evar ret).enode )
      | Linteger, [l; u; {term_node= Tlambda ([q], t)}], "\\sum" ->
          self#translate_lambda l u q t zero "sum" (do_op PlusA)
      | Linteger, [l; u; {term_node= Tlambda ([q], t)}], "\\product" ->
          self#translate_lambda l u q t one "product" (do_op Mult)
      | Linteger, [l; u; {term_node= Tlambda ([q], t)}], "\\numof" ->
          let inc_if r l =
            Env.mk_if (cmp Rneq l zero)
              (Env.make [] [self#cbinop_ui PlusA r r one] [])
              Env.empty
          in
          self#translate_lambda l u q t zero "numof" inc_if
      | Linteger, _, _ -> (
          let app = Logic_const.term (Tapp (li, ll, params)) Linteger in
          let inlined_app = Inline.term app in
          match inlined_app.term_node with
          | Tapp _ ->
              (* cheap equality test *)
              (* doesn't work if it yields a \lambda term *)
              raise Unsupported
          | _ -> self#translate_term_node inlined_app )
      | Lreal, _, _ -> raise Unsupported
      | Ctype ty, _, _ ->
          let rpl_functions =
            Options.Replace_Functions.get ()
            |> Utils.split ','
            |> List.map (Utils.split '/')
          in
          let rec aux = function
            | (h1 :: h2 :: _) :: t ->
                if h1 = fname then
                  let args_env, args_var =
                    List.map self#translate_term params |> List.split
                  in
                  let env = List.fold_left Env.merge Env.empty args_env in
                  let ret = self#fresh_varinfo Cil.intType ("call_" ^ fname) in
                  let fct = Cil.evar (Cil.makeVarinfo false false h2 ty) in
                  let ret_lval = (Var ret, NoOffset) in
                  let call =
                    Cil.mkStmt
                      (Instr (Call (Some ret_lval, fct, args_var, loc)))
                  in
                  ( Env.merge env (Env.make [ret] [call] [])
                  , (Cil.evar ret).enode )
                else aux t
            | [_]::_ | []::_ | [] ->
                Options.failure ~current:true ~once:true
                  "call of logic function %s unsupported, you may replace it \
                   with a C function"
                  fname ;
                raise Unsupported
          in
          aux rpl_functions
      | _ -> raise Unsupported

    method private translate_cast ty t =
      match t.term_type with
      (* source type *)
      | Linteger ->
          let env, e = self#translate_term t in
          let ret = self#fresh_varinfo ty "cast" in
          let get =
            if Cil.isUnsignedInteger ty then self#cget_ui else self#cget_si
          in
          let i_1 = get (Cil.var ret) e in
          (Env.merge env (Env.make [ret] [i_1] []), (Cil.evar ret).enode)
      | Lreal -> raise Unsupported
      | Ctype _ ->
          let env, e = self#translate_term t in
          (env, CastE (ty, e))
      | _ -> raise Unreachable

    method private translate_term_node t =
      match t.term_node with
      | TConst c ->
          let i, e = self#translate_constant t.term_type c in
          (i, e)
      | TLval tl ->
          let env, lv = self#translate_lval tl in
          (env, Lval lv)
      | TSizeOf ty -> (Env.empty, SizeOf ty)
      | TSizeOfE t ->
          let env, e = self#translate_term t in
          (env, SizeOfE e)
      | TSizeOfStr str -> (Env.empty, SizeOfStr str)
      | TAlignOf ty -> (Env.empty, AlignOf ty)
      | TAlignOfE t ->
          let env, e = self#translate_term t in
          (env, AlignOfE e)
      | TUnOp (op, t) -> self#translate_unop op t
      | TBinOp (op, a, b) -> self#translate_binop t.term_type op a b
      | TCastE (ty, t) -> self#translate_cast ty t
      | TAddrOf (TMem x, TIndex (y, TNoOffset)) ->
          let x' = Cil.mkTermMem ~addr:x ~off:TNoOffset in
          let ty = Utils.type_of_pointed (Cil.typeOfTermLval x') in
          let x' = Logic_const.term (TLval x') ty in
          self#translate_term_node {t with term_node= TBinOp (PlusPI, x', y)}
      | TAddrOf tl ->
          let env, lv = self#translate_lval tl in
          (env, AddrOf lv)
      | TStartOf tl ->
          let env, lv = self#translate_lval tl in
          (env, StartOf lv)
      | Tapp (li, ll, params) -> self#translate_app li ll params
      | Tif (x, y, z) -> self#translate_tif x y z
      | Tat (t, l) -> self#translate_at t l
      | Tnull -> (Env.empty, zero.enode)
      | TLogic_coerce (lt, t) -> self#translate_logic_coerce lt t
      | Tlambda _ | TDataCons _ | Tbase_addr _ | Toffset _ | Tblock_length _
       |TUpdate _ | Ttypeof _ | Ttype _ | Tempty_set | Tunion _ | Tinter _
       |Tcomprehension _ | Trange _ | Tlet _ ->
          raise Unsupported

    method private translate_term t =
      let env, enode = self#translate_term_node t in
      (env, Cil.new_exp ~loc enode)

    method private translate_lhost =
      function
      | TVar lv -> (Env.empty, Var (self#translate_var lv))
      | TResult _ -> (Env.empty, Var (Extlib.the result_varinfo))
      | TMem t ->
          let env, t = self#translate_term t in
          (env, Mem t)

    method private translate_offset =
      function
      | TNoOffset -> (Env.empty, NoOffset)
      | TField (fi, o) ->
          let env, o' = self#translate_offset o in
          (env, Field (fi, o'))
      | TModel _ -> raise Unsupported
      | TIndex (t, o) ->
          let env1, e = self#as_c_type Cil.intType t in
          let env2, o' = self#translate_offset o in
          (Env.merge env1 env2, Index (e, o'))

    method private translate_lval (a, b) =
      let aux () =
        let env1, a' = self#translate_lhost a in
        let env2, b' = self#translate_offset b in
        (Env.merge env1 env2, (a', b'))
      in
      match Cil.typeOfTermLval (a, b) with
      | Linteger ->
          let fresh_var = self#fresh_Z_varinfo "lval" in
          let env, t' = aux () in
          let e_t = Cil.new_exp ~loc (Lval t') in
          let i_1 = self#cinit_set (Cil.evar fresh_var) e_t in
          let i_2 = self#cclear (Cil.evar fresh_var) in
          (Env.merge env (Env.make [fresh_var] [i_1] [i_2]), Cil.var fresh_var)
      | Lreal -> raise Unsupported
      | _ -> aux ()

    method private translate_predicate p =
      self#translate_predicate_node p.pred_content

    method private translate_rel rel t1 t2 =
      match (t1.term_type, t2.term_type) with
      | Linteger, Ctype x ->
          let env1, t1' = self#translate_term t1 in
          let env2, t2' = self#translate_term t2 in
          let varname = Utils.relation_to_string rel in
          let v = self#fresh_bool_varinfo varname in
          let zcmp =
            if Cil.isUnsignedInteger x then self#ccmp_ui else self#ccmp_si
          in
          let i = zcmp (Cil.var v) t1' t2' in
          ( Env.merge env1 (Env.merge env2 (Env.make [v] [i] []))
          , cmp rel (Cil.evar v) zero )
      | Lreal, Lreal -> raise Unsupported
      | Linteger, Linteger | Ctype _, Linteger ->
          let env1, t1' = self#as_logic_type Linteger t1 in
          let env2, t2' = self#translate_term t2 in
          let varname = Utils.relation_to_string rel in
          let v = self#fresh_bool_varinfo varname in
          let i = self#ccmp (Cil.var v) t1' t2' in
          ( Env.merge env1 (Env.merge env2 (Env.make [v] [i] []))
          , cmp rel (Cil.evar v) zero )
      | _ ->
          let env1, t1' = self#translate_term t1 in
          let env2, t2' = self#translate_term t2 in
          (Env.merge env1 env2, cmp rel t1' t2')

    method private translate_and p q =
      let var = self#fresh_bool_varinfo "and" in
      let env, pred1_var = self#translate_predicate p in
      let i_1 = mk_affect (Cil.var var) pred1_var in
      let if_env =
        let env, pred2_var = self#translate_predicate q in
        Env.merge env (Env.make [] [mk_affect (Cil.var var) pred2_var] [])
      in
      let i_2 = Env.mk_if (Cil.evar var) if_env Env.empty in
      (Env.merge env (Env.make [var] [i_1; i_2] []), Cil.evar var)

    method private translate_or p q =
      let var = self#fresh_bool_varinfo "or" in
      let env, pred1_var = self#translate_predicate p in
      let i_1 = mk_affect (Cil.var var) pred1_var in
      let if_env =
        let env, pred2_var = self#translate_predicate q in
        Env.merge env (Env.make [] [mk_affect (Cil.var var) pred2_var] [])
      in
      let i_2 = Env.mk_if (Cil.evar var) Env.empty if_env in
      (Env.merge env (Env.make [var] [i_1; i_2] []), Cil.evar var)

    method private translate_implies p q =
      let var = self#fresh_bool_varinfo "implies" in
      let i_1 = mk_affect (Cil.var var) one in
      let env, pred1_var = self#translate_predicate p in
      let if_env =
        let env, pred2_var = self#translate_predicate q in
        Env.merge env (Env.make [] [mk_affect (Cil.var var) pred2_var] [])
      in
      let i_2 = Env.mk_if pred1_var if_env Env.empty in
      (Env.merge env (Env.make [var] [i_1; i_2] []), Cil.evar var)

    method private translate_equiv p q =
      let env1, pred1_var = self#translate_predicate p in
      let env2, pred2_var = self#translate_predicate q in
      let not_pred1_var =
        Cil.new_exp ~loc (UnOp (LNot, pred1_var, Cil.intType))
      in
      let not_pred2_var =
        Cil.new_exp ~loc (UnOp (LNot, pred2_var, Cil.intType))
      in
      let exp1 = Cil.mkBinOp ~loc LOr not_pred1_var pred2_var in
      let exp2 = Cil.mkBinOp ~loc LOr not_pred2_var pred1_var in
      (Env.merge env1 env2, Cil.mkBinOp ~loc LAnd exp1 exp2)

    method private translate_not p =
      let env, p' = self#translate_predicate p in
      (env, Cil.new_exp ~loc (UnOp (LNot, p', Cil.intType)))

    method private translate_pif t p q =
      let env1, t_var = self#translate_term t in
      let res_var = self#fresh_bool_varinfo "pif" in
      let cond, env2 =
        match t.term_type with
        | Linteger ->
            let tmp = self#fresh_bool_varinfo "pif_cmp" in
            let i_1 = self#ccmp_si (Cil.var tmp) t_var zero in
            (cmp Rneq (Cil.evar tmp) zero, Env.make [tmp] [i_1] [])
        | Lreal -> raise Unsupported
        | Ctype (TInt _) -> (cmp Rneq t_var zero, Env.empty)
        | Ltype _ as lt when Logic_const.is_boolean_type lt ->
            (cmp Rneq t_var zero, Env.empty)
        | _ -> raise Unreachable
      in
      let e, pred1_var = self#translate_predicate p in
      let then_env =
        Env.merge e (Env.make [] [mk_affect (Cil.var res_var) pred1_var] [])
      in
      let e, pred2_var = self#translate_predicate q in
      let else_env =
        Env.merge e (Env.make [] [mk_affect (Cil.var res_var) pred2_var] [])
      in
      let i_1 = Env.mk_if cond then_env else_env in
      (Env.merge env1 (Env.merge env2 (Env.make [] [i_1] [])), Cil.evar res_var)

    method private translate_valid term =
      match term.term_node with
      | Tempty_set -> (Env.empty, one)
      | TBinOp ((PlusPI | IndexPI), p, {term_node= Trange (Some x, Some y)}) ->
          self#translate_valid_ptr_range p x y
      | TBinOp ((PlusPI | IndexPI), p, x) ->
          self#translate_valid_ptr_offset p x
      | TBinOp (MinusPI, p, x) ->
          let einfo = {exp_type= x.term_type; exp_name= []} in
          let x = Cil.term_of_exp_info loc (TUnOp (Neg, x)) einfo in
          self#translate_valid_ptr_offset p x
      | TLval _ -> self#translate_valid_ptr term
      | TAddrOf (TMem x, TIndex (y, TNoOffset)) ->
          let x' = Cil.mkTermMem ~addr:x ~off:TNoOffset in
          let ty = Utils.type_of_pointed (Cil.typeOfTermLval x') in
          let x' = Logic_const.term (TLval x') ty in
          self#translate_valid {term with term_node= TBinOp (PlusPI, x', y)}
      | TAddrOf ((TVar x, TIndex (y, TNoOffset)) as v) ->
          let ty = Cil.typeOfTermLval v in
          let x' = Logic_const.term (TLval (TVar x, TNoOffset)) ty in
          self#translate_valid {term with term_node= TBinOp (PlusPI, x', y)}
      | TStartOf _ -> self#translate_valid_ptr term
      | _ -> Utils.error_term term

    method private translate_valid_ptr_range pointer min_off max_off =
      let env1, x' = self#translate_term pointer in
      let env2, low_o = self#as_c_type Cil.intType min_off in
      let env3, up_o = self#as_c_type Cil.intType max_off in
      let ret = self#fresh_bool_varinfo "valid" in
      let dim = self#fresh_varinfo Cil.intType "valid_dim" in
      let cond = cmp Rle low_o up_o in
      let i_2 = self#cpc_dim (Cil.var dim) x' in
      let e1 = cmp Rge up_o zero in
      let e2 = cmp Rgt (Cil.evar dim) up_o in
      let e_binop = Cil.mkBinOp ~loc LAnd e1 e2 in
      let i_3 = mk_affect (Cil.var ret) e_binop in
      let env_then = Env.make [dim] [i_2; i_3] [] in
      let env_else = Env.make [] [mk_affect (Cil.var ret) one] [] in
      let i_if = Env.mk_if cond env_then env_else in
      ( Env.merge env1
          (Env.merge env2 (Env.merge env3 (Env.make [ret] [i_if] [])))
      , Cil.evar ret )

    method private translate_valid_ptr_offset pointer offset =
      let loc = pointer.term_loc in
      let env1, x' = self#translate_term pointer in
      let env2, y' = self#as_c_type Cil.intType offset in
      let ret = self#fresh_bool_varinfo "valid" in
      let dim = self#fresh_varinfo Cil.intType "valid_dim" in
      let i_1 = self#cpc_dim (Cil.var dim) x' in
      let e1 = cmp Rge y' zero in
      let e2 = cmp Rgt (Cil.evar dim) y' in
      let i_2 = mk_affect (Cil.var ret) (Cil.mkBinOp ~loc LAnd e1 e2) in
      let env3 = Env.make [ret; dim] [i_1; i_2] [] in
      (Env.merge env1 (Env.merge env2 env3), Cil.evar ret)

    method private translate_valid_ptr pointer =
      let env, x' = self#translate_term pointer in
      let ret = self#fresh_bool_varinfo "valid" in
      let dim = self#fresh_varinfo Cil.intType "valid_dim" in
      let i_1 = self#cpc_dim (Cil.var dim) x' in
      let e2 = cmp Rgt (Cil.evar dim) zero in
      let i_2 = mk_affect (Cil.var ret) e2 in
      (Env.merge env (Env.make [ret; dim] [i_1; i_2] []), Cil.evar ret)

    method private translate_forall = self#translate_quantif ~forall:true

    method private translate_exists = self#translate_quantif ~forall:false

    method private translate_quantif ~forall logic_vars hyps goal =
      let varname = if forall then "forall" else "exists" in
      let var = self#fresh_bool_varinfo varname in
      let init_val = if forall then one else zero in
      let i_1 = mk_affect (Cil.var var) init_val in
      let negate exp = Cil.new_exp ~loc (UnOp (LNot, exp, Cil.intType)) in
      let cond = if forall then Cil.evar var else negate (Cil.evar var) in
      let on_lvar (i_b, e_c, i_i) lvar =
        let t1, r1, r2, t2 = Utils.extract_guards lvar hyps in
        let t1, r1, r2, t2 =
          try (Extlib.the t1, Extlib.the r1, Extlib.the r2, Extlib.the t2)
          with _ ->
            let pp_opt_op fmt = function
              | None -> Format.fprintf fmt "??"
              | Some op -> Format.fprintf fmt "%a" Printer.pp_relation op
            in
            let pp_opt_var fmt = function
              | None -> Format.fprintf fmt "??"
              | Some var -> Format.fprintf fmt "%a" Printer.pp_term var
            in
            Options.warning ~current:true ~once:true
              "imprecise bounds for quantified variable %a (%a %a %a %a %a)"
              Printer.pp_logic_var lvar pp_opt_var t1 pp_opt_op r1
              Printer.pp_logic_var lvar pp_opt_op r2 pp_opt_var t2 ;
            raise Unsupported
        in
        let iter_name = lvar.lv_name in
        let i_before, e_cond, i_inside =
          match t1.term_type with
          | Linteger ->
              let it = my_Z_varinfo iter_name in
              let env1, t1' = self#translate_term t1 in
              let env2, t2' = self#translate_term t2 in
              let i_3 = self#cinit_set (Cil.evar it) t1' in
              let inc exp = self#cbinop_ui PlusA exp exp one in
              let i_4 = if r1 = Rlt then [inc (Cil.evar it)] else [] in
              let tmp = self#fresh_bool_varinfo (varname ^ "_cmp") in
              let ins_b_2 =
                self#cbinop_ui PlusA (Cil.evar it) (Cil.evar it) one
              in
              let e1 = cmp r2 (Cil.evar tmp) zero in
              let i_8 = self#cclear (Cil.evar it) in
              let cmp =
                match t2.term_type with
                | Linteger -> self#ccmp
                | Lreal -> raise Unsupported
                | _ -> self#ccmp_si
              in
              let i_6 = cmp (Cil.var tmp) (Cil.evar it) t2' in
              let ins_b_3 = cmp (Cil.var tmp) (Cil.evar it) t2' in
              let i_before =
                Env.merge env1
                  (Env.merge env2
                     (Env.make [it; tmp] ((i_3 :: i_4) @ [i_6]) [i_8]))
              in
              (i_before, e1, [ins_b_2; ins_b_3])
          | Lreal -> raise Unsupported
          | _ ->
              let iter = my_varinfo Cil.intType iter_name in
              let env1, t1' = self#translate_term t1 in
              let env2, t2' = self#translate_term t2 in
              let op =
                match r1 with
                | Rlt -> Cil.mkBinOp ~loc PlusA t1' one
                | Rle -> t1'
                | _ -> raise Unsupported
              in
              let e1 = cmp r2 (Cil.evar iter) t2' in
              let e_binop = Cil.mkBinOp ~loc PlusA (Cil.evar iter) one in
              let i_init = mk_affect (Cil.var iter) op in
              let i_before =
                Env.merge env1 (Env.merge env2 (Env.make [iter] [i_init] []))
              in
              (i_before, e1, [mk_affect (Cil.var iter) e_binop])
        in
        ( Env.merge i_b i_before
        , Cil.mkBinOp ~loc LAnd e_cond e_c
        , List.rev_append (List.rev i_i) i_inside )
      in
      let env_before, e_cond, i_inside =
        List.fold_left on_lvar (Env.empty, cond, []) logic_vars
      in
      let env1, goal_var = self#translate_predicate goal in
      let i_inside = mk_affect (Cil.var var) goal_var :: i_inside in
      let env_loop = Env.merge env1 (Env.make [] i_inside []) in
      let i_loop = Env.mk_loop e_cond env_loop in
      let env_block = Env.merge env_before (Env.make [] [i_loop] []) in
      (Env.make [var] [i_1; Env.mk_block env_block] [], Cil.evar var)

    method private translate_predicate_node =
      function
      | Pfalse -> (Env.empty, zero)
      | Ptrue -> (Env.empty, one)
      | Prel (r, t1, t2) -> self#translate_rel r t1 t2
      | Pand (p, q) -> self#translate_and p q
      | Por (p, q) -> self#translate_or p q
      | Pimplies (p, q) -> self#translate_implies p q
      | Piff (p, q) -> self#translate_equiv p q
      | Pnot p -> self#translate_not p
      | Pif (t, p, q) -> self#translate_pif t p q
      | Pforall (vars, {pred_content= Pimplies (h, g)}) ->
          self#translate_forall vars h g
      | Pexists (vars, {pred_content= Pand (h, g)}) ->
          self#translate_exists vars h g
      | Pat (p, BuiltinLabel Here) -> self#translate_predicate p
      | Pvalid (_, t) -> self#translate_valid t
      | Pvalid_read (_, t) ->
          Options.warning ~current:true ~once:true
            "\\valid_read(%a) is interpreted as \\valid(%a)" Printer.pp_term t
            Printer.pp_term t ;
          self#translate_valid t
      | Pforall _ as p ->
          Options.warning ~current:true ~once:true
            "%a not of the form \\forall ...; a ==> b"
            Printer.pp_predicate_node p ;
          raise Unsupported
      | Pexists _ as p ->
          Options.warning ~current:true ~once:true
            "%a not of the form \\exists ...; a && b" Printer.pp_predicate_node
            p ;
          raise Unsupported
      | Papp _ | Pseparated _ | Pxor _ | Plet _ | Pat _ | Pinitialized _
       |Pfresh _ | Pdangling _ | Pallocable _ | Pfreeable _
       |Pvalid_function _ ->
          raise Unsupported

    (* modify result_varinfo when the function returns something *)
    method private compute_result_varinfo fct =
      let rec do_stmts = function
        | [] -> ()
        | {skind= Return (Some {enode= Lval (Var v, _)}, _)} :: _ ->
            result_varinfo <- Some v
        | _ :: t -> do_stmts t
      in
      do_stmts fct.sallstmts

    method private at_least_one_prop kf behaviors kloc =
      let to_prop b k = Property.ip_of_ensures kf kloc b k in
      let in_ensures b r k = r || List.mem (to_prop b k) props in
      let in_bhv r b =
        r || List.fold_left (in_ensures b) false b.b_post_cond
      in
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
          let env, v =
            self#translate_predicate (Inline.pred pred.ip_content)
          in
          let e = Cil.new_exp ~loc (UnOp (LNot, v, Cil.intType)) in
          let env_ret = Env.make [] [mk_ret zero] [] in
          Env.merge env (Env.make [] [Env.mk_if e env_ret Env.empty] [])
        with Unsupported ->
          Options.warning ~current:true ~once:true "%a unsupported"
            Printer.pp_predicate pred.ip_content ;
          Env.empty
      in
      let do_behavior env b =
        let requires = List.filter not_translated b.b_requires in
        let typically = List.filter not_translated (Utils.typically_preds b) in
        let to_prop = Property.ip_of_requires kf kloc b in
        let in_props p = List.mem (to_prop p) props in
        let requires, typically =
          if pre_entry_point then (requires, typically)
          else (List.filter in_props requires, List.filter in_props typically)
        in
        let do_requires env pred =
          if pre_entry_point then Env.merge env (translate_as_return pred)
          else
            let prop = to_prop pred in
            Env.merge env (self#pc_assert_exception pred.ip_content "" prop)
        in
        let do_typically env pred =
          if pre_entry_point then Env.merge env (translate_as_return pred)
          else env
        in
        if requires <> [] || typically <> [] then
          let inserts' = List.fold_left do_typically Env.empty typically in
          let inserts = List.fold_left do_requires inserts' requires in
          if b.b_assumes <> [] then
            let env', exp = self#cond_of_assumes b.b_assumes in
            let i_1 = Env.mk_if exp inserts Env.empty in
            Env.merge env (Env.merge env' (Env.make [] [i_1] []))
          else Env.merge env inserts
        else env
      in
      List.fold_left do_behavior Env.empty behaviors

    method private post kf behaviors kloc =
      let do_behavior env b =
        let post = b.b_post_cond in
        let to_prop = Property.ip_of_ensures kf kloc b in
        let post = List.filter (fun x -> List.mem (to_prop x) props) post in
        let do_postcond env (tk, pred) =
          let prop = to_prop (tk, pred) in
          Env.merge env (self#pc_assert_exception pred.ip_content "" prop)
        in
        if post <> [] then
          if b.b_assumes <> [] then
            let env1, exp = self#cond_of_assumes b.b_assumes in
            let env2 = List.fold_left do_postcond Env.empty post in
            let i_1 = Env.mk_if exp env2 Env.empty in
            Env.merge env (Env.merge env1 (Env.make [] [i_1] []))
          else Env.merge env (List.fold_left do_postcond Env.empty post)
        else env
      in
      List.fold_left do_behavior Env.empty behaviors

    (* alloc and dealloc variables for \at terms *)
    method private save_varinfo kf vi =
      let rec dig_type = function
        | TPtr (ty, _) | TArray (ty, _, _, _) -> ty
        | TNamed (ty, _) -> dig_type ty.ttype
        | _ -> raise Unreachable
      in
      let rec strip_const = function
        | TPtr (t, att) -> TPtr (strip_const t, att)
        | TArray (t, a, b, c) -> TArray (strip_const t, a, b, c)
        | ty -> ty
      in
      let addoffset ty lval exp =
        if Cil.isPointerType ty then
          let base = Cil.new_exp ~loc (Lval lval) in
          (Mem (Cil.new_exp ~loc (BinOp (IndexPI, base, exp, ty))), NoOffset)
        else if Cil.isArrayType ty then
          Cil.addOffsetLval (Index (exp, NoOffset)) lval
        else raise Unreachable
      in
      let lengths = Infer.lengths_from_requires kf in
      let terms =
        try Cil_datatype.Varinfo.Hashtbl.find lengths vi with _ -> []
      in
      let do_varinfo v =
        let vtype = Utils.unname v.vtype in
        let my_old_v = my_varinfo (strip_const vtype) ("old_" ^ v.vname) in
        let insert_before = mk_affect (Cil.var my_old_v) (Cil.evar v) in
        let rec alloc_aux my_old_ptr my_ptr ty = function
          | h :: t ->
              let ty = dig_type ty in
              let env, h' = self#as_c_type Cil.ulongType h in
              let my_iterator = self#fresh_varinfo Cil.ulongType "iter" in
              let e1 = Cil.new_exp ~loc (SizeOf ty) in
              let e2 = Cil.mkBinOp ~loc Mult h' e1 in
              let i_1 = self#cmalloc my_old_ptr e2 in
              let my_new_old_ptr =
                addoffset vtype my_old_ptr (Cil.evar my_iterator)
              in
              let my_new_ptr = addoffset vtype my_ptr (Cil.evar my_iterator) in
              let env_block = alloc_aux my_new_old_ptr my_new_ptr ty t in
              let i_2 = mk_affect (Cil.var my_iterator) zero in
              let cond = cmp Rlt (Cil.evar my_iterator) h' in
              let e3 = Cil.mkBinOp ~loc PlusA (Cil.evar my_iterator) one in
              let env_aff =
                Env.make [] [mk_affect (Cil.var my_iterator) e3] []
              in
              let env_body = Env.merge env_block env_aff in
              let i_3 = Env.mk_loop cond env_body in
              Env.merge env (Env.make [my_iterator] [i_1; i_2; i_3] [])
          | [] ->
              Env.make []
                [mk_affect my_old_ptr (Cil.new_exp ~loc (Lval my_ptr))]
                []
        in
        if Cil.isPointerType vtype || Cil.isArrayType vtype then
          let my_old_ptr =
            my_varinfo (strip_const vtype) ("old_ptr_" ^ v.vname)
          in
          let ins = alloc_aux (Cil.var my_old_ptr) (Cil.var v) vtype terms in
          Env.merge (Env.make [my_old_v; my_old_ptr] [insert_before] []) ins
        else Env.make [my_old_v] [insert_before] []
      in
      let env_before = do_varinfo vi in
      let do_varinfo v =
        let vtype = Utils.unname v.vtype in
        let rec dealloc_aux my_old_ptr = function
          | [] -> Env.empty
          | [_] ->
              Env.make [] [self#cfree (Cil.new_exp ~loc (Lval my_old_ptr))] []
          | h :: t ->
              let my_iterator = self#fresh_varinfo Cil.ulongType "iter" in
              let env, h' = self#as_c_type Cil.ulongType h in
              let aux = addoffset vtype my_old_ptr (Cil.evar my_iterator) in
              let env_block = dealloc_aux aux t in
              let cond = cmp Rlt (Cil.evar my_iterator) h' in
              let e1 = Cil.mkBinOp ~loc PlusA (Cil.evar my_iterator) one in
              let e = Cil.new_exp ~loc (Lval my_old_ptr) in
              let env_aff =
                Env.make [] [mk_affect (Cil.var my_iterator) e1] []
              in
              let env_body = Env.merge env_block env_aff in
              let i_2 = Env.mk_loop cond env_body in
              let i_1 = mk_affect (Cil.var my_iterator) zero in
              let i_3 = self#cfree e in
              Env.merge env (Env.make [my_iterator] [i_1; i_2; i_3] [])
        in
        if Cil.isPointerType vtype || Cil.isArrayType vtype then
          let my_old_ptr = my_varinfo vtype ("old_ptr_" ^ v.vname) in
          dealloc_aux (Cil.var my_old_ptr) terms
        else Env.empty
      in
      let env_after = do_varinfo vi in
      (env_before, env_after)

    method! vfunc f =
      let entry_point =
        Kernel_function.get_name (fst (Globals.entry_point ()))
      in
      let kf = Globals.Functions.find_by_name f.svar.vname in
      let behaviors = Annotations.behaviors kf in
      self#compute_result_varinfo f ;
      (let pre_entry_point = f.svar.vname = entry_point in
       if pre_entry_point then
         let pre_varinfo =
           match f.svar.vtype with
           | TFun (_, x, y, z) ->
               { f.svar with
                 vname= f.svar.vname ^ "_precond"
               ; vtype= TFun (Cil.intType, x, y, z) }
           | _ -> assert false
         in
         let env_pre = self#pre ~pre_entry_point kf behaviors Kglobal in
         let stmts =
           List.rev_append
             (List.rev (Env.stmts env_pre))
             (List.rev_append (List.rev (Env.cleans env_pre)) [mk_ret one])
         in
         let formals = f.sformals and locals = Env.locals env_pre in
         let pre_fun = Utils.mk_fundec pre_varinfo ~formals ~locals stmts in
         functions <- pre_fun :: functions
       else
         let label_pre = Symbolic_label.beg_func f.svar.vname in
         let env = self#pre ~pre_entry_point kf behaviors Kglobal in
         self#insert label_pre env) ;
      ( if self#at_least_one_prop kf behaviors Kglobal then
        let env = self#post kf behaviors Kglobal in
        let label = Symbolic_label.end_func f.svar.vname in
        self#insert label (Env.make [] [Env.mk_block env] []) ) ;
      let do_varinfo v =
        let env_before, env_after = self#save_varinfo kf v in
        let beg_label = Symbolic_label.beg_func f.svar.vname
        and end_label = Symbolic_label.end_func f.svar.vname in
        self#insert beg_label env_before ;
        self#insert end_label env_after
      in
      List.iter do_varinfo visited_globals ;
      List.iter do_varinfo (Kernel_function.get_formals kf) ;
      Cil.DoChildren

    method private cond_of_assumes pred_list =
      let rec aux acc ret = function
        | [] -> (acc, ret)
        | h :: t ->
            let env, v = self#translate_predicate (Inline.pred h.ip_content) in
            let e = Cil.mkBinOp ~loc LAnd ret v in
            aux (Env.merge acc env) e t
      in
      aux Env.empty one pred_list

    method private cond_of_behaviors pred_lists =
      let rec aux acc ret = function
        | [] -> (acc, ret)
        | h :: t ->
            let env, v = self#cond_of_assumes h in
            let e = Cil.mkBinOp ~loc LOr ret v in
            aux (Env.merge acc env) e t
      in
      aux Env.empty zero pred_lists

    method private pc_exc str i =
      let rec aux ret = function
        | [] -> ret
        | [h] -> aux (ret ^ string_of_int h) []
        | h :: t -> aux (ret ^ string_of_int h ^ ",") t
      in
      let swd_str =
        if swd = [] then "" else Format.sprintf "%s$" (aux "" swd)
      in
      let str = Cil.mkString ~loc (swd_str ^ str) in
      let const = CInt64 (Integer.of_int i, IInt, Some (string_of_int i)) in
      self#cpc_exc str (Cil.new_exp ~loc (Const const))

    method private pc_ass str i =
      let str = Cil.mkString ~loc str in
      let const = CInt64 (Integer.of_int i, IInt, Some (string_of_int i)) in
      self#cpc_assume str (Cil.new_exp ~loc (Const const))

    method private pc_to_fc str = self#cpc_to_fc (Cil.mkString ~loc str)

    method private pc_assert_exception pred msg prop =
      try
        let env, var = self#translate_predicate (Inline.pred pred) in
        let e = Cil.new_exp ~loc (UnOp (LNot, var, Cil.intType)) in
        let id = Utils.to_id prop in
        let i_1 =
          Env.mk_if e (Env.make [] [self#pc_exc msg id] []) Env.empty
        in
        translated_properties <- prop :: translated_properties ;
        Env.merge env (Env.make [] [i_1] [])
      with Unsupported ->
        Options.warning ~current:true ~once:true "%a unsupported"
          Printer.pp_predicate pred ;
        Env.empty

    method private pc_assume pred =
      try
        let env, var = self#translate_predicate (Inline.pred pred) in
        let e = Cil.new_exp ~loc (UnOp (LNot, var, Cil.intType)) in
        let env_assert = Env.make [] [self#pc_ass "" 0] [] in
        Env.merge env (Env.make [] [Env.mk_if e env_assert Env.empty] [])
      with Unsupported ->
        Options.warning ~current:true ~once:true "%a unsupported"
          Printer.pp_predicate pred ;
        Env.empty

    method private for_behaviors bhvs env =
      if bhvs = [] then env
      else
        let env', cond = self#cond_of_behaviors bhvs in
        Env.merge env' (Env.make [] [Env.mk_if cond env Env.empty] [])

    method private translate_stmt_spec kf stmt bhvs spec =
      if self#at_least_one_prop kf spec.spec_behavior (Kstmt stmt) then
        let stmt_bhvs = spec.spec_behavior in
        let ins_1 =
          self#pre ~pre_entry_point:false kf stmt_bhvs (Kstmt stmt)
        in
        let ins_1 = self#for_behaviors bhvs ins_1 in
        let ins_2 = self#post kf stmt_bhvs (Kstmt stmt) in
        let ins_2 =
          if bhvs = [] then ins_2 else self#for_behaviors bhvs ins_2
        in
        [ (Symbolic_label.beg_stmt stmt.sid, ins_1)
        ; (Symbolic_label.end_stmt stmt.sid, ins_2) ]
      else []

    method private translate_assert kf stmt ca for_behaviors pred =
      let prop = Property.ip_of_code_annot_single kf stmt ca in
      if List.mem prop props then
        let ins = self#pc_assert_exception pred "" prop in
        [ ( Symbolic_label.beg_stmt stmt.sid
          , self#for_behaviors for_behaviors ins ) ]
      else []

    method private translate_invariant kf stmt ca for_behaviors pred =
      let prop = Property.ip_of_code_annot_single kf stmt ca in
      if List.mem prop props then
        let i_1 = self#pc_assert_exception pred "not established" prop in
        let i_2 = self#pc_assert_exception pred "not preserved" prop in
        [ ( Symbolic_label.beg_stmt stmt.sid
          , self#for_behaviors for_behaviors i_1 )
        ; ( Symbolic_label.end_iter stmt.sid
          , self#for_behaviors for_behaviors i_2 ) ]
      else []

    method private translate_variant kf stmt ca term =
      let prop = Property.ip_of_code_annot_single kf stmt ca in
      translated_properties <- prop :: translated_properties ;
      if List.mem prop props then
        let id = Utils.to_id prop in
        let beg_label = Symbolic_label.beg_iter stmt.sid
        and end_label = Symbolic_label.end_iter stmt.sid in
        match term.term_type with
        | Linteger ->
            (* at BegIter *)
            let env_1, beg_variant = self#translate_term term in
            let env_1' = Env.make (Env.locals env_1) (Env.stmts env_1) [] in
            let var_1 = self#fresh_bool_varinfo "variant_pos" in
            let pce_1 = self#pc_exc "non positive" id in
            let i_1_1 = self#ccmp_ui (Cil.var var_1) beg_variant zero in
            let cond_1 = cmp Rlt (Cil.evar var_1) zero in
            let i_1_2 = Env.mk_if cond_1 (Env.make [] [pce_1] []) Env.empty in
            (* at EndIter *)
            let env_2, end_variant = self#translate_term term in
            let var_2 = self#fresh_bool_varinfo "variant_decr" in
            let pce_2 = self#pc_exc "non decreasing" id in
            let i_2_1 = self#ccmp (Cil.var var_2) end_variant beg_variant in
            let cond_2 = cmp Rge (Cil.evar var_2) zero in
            let i_2_2 = Env.mk_if cond_2 (Env.make [] [pce_2] []) Env.empty in
            [ (beg_label, Env.merge env_1' (Env.make [var_1] [i_1_1; i_1_2] []))
            ; ( end_label
              , Env.merge env_2
                  (Env.make [var_2] [i_2_1; i_2_2] (Env.cleans env_1)) ) ]
        | Lreal -> raise Unsupported
        | _ ->
            (* at BegIter *)
            let env_1, beg_variant = self#translate_term term in
            let cond_1 = cmp Rlt beg_variant zero in
            let pce_1 = self#pc_exc "non positive" id in
            let var_1 = self#fresh_varinfo Cil.intType "variant_save" in
            let if_1 = Env.mk_if cond_1 (Env.make [] [pce_1] []) Env.empty in
            let aff_1 = mk_affect (Cil.var var_1) beg_variant in
            (* at EndIter *)
            let env_2, end_variant = self#translate_term term in
            let cond_2 = cmp Rge end_variant (Cil.evar var_1) in
            let pce_2 = self#pc_exc "non decreasing" id in
            let if_2 = Env.mk_if cond_2 (Env.make [] [pce_2] []) Env.empty in
            [ (beg_label, Env.merge env_1 (Env.make [var_1] [if_1; aff_1] []))
            ; (end_label, Env.merge env_2 (Env.make [] [if_2] [])) ]
      else []

    method! vcode_annot ca =
      let stmt = Extlib.the self#current_stmt in
      let kf = Kernel_function.find_englobing_kf stmt in
      let bhv_names =
        match ca.annot_content with
        | AAssert (b, _,_) | AStmtSpec (b, _) | AInvariant (b, _, _) -> b
        | _ -> []
      in
      let on_behavior s _ b ret = if b.b_name = s then b.b_assumes else ret in
      let on_behavior_name s =
        Annotations.fold_behaviors (on_behavior s) kf []
      in
      let bhvs = List.map on_behavior_name bhv_names in
      let ins =
        match ca.annot_content with
        | AStmtSpec (_, spec) -> self#translate_stmt_spec kf stmt bhvs spec
        | AAssert (_, _, pred) -> self#translate_assert kf stmt ca bhvs pred
        | AInvariant (_, true, pred) ->
            self#translate_invariant kf stmt ca bhvs pred
        | AVariant (term, _) -> self#translate_variant kf stmt ca term
        | _ -> []
      in
      let on_labeled_ins (label, ins) = self#insert label ins in
      List.iter on_labeled_ins ins ;
      Cil.DoChildren

    method private assigns_swd assigns =
      let assigns_terms =
        match List.fold_left Logic_utils.merge_assigns WritesAny assigns with
        | WritesAny ->
            Options.warning ~current:true ~once:true
              "assigns clause not precise enough" ;
            []
        | Writes terms -> List.map fst terms
      in
      let on_term ret term =
        let t = term.it_content in
        match t.term_node with
        | TLval
            ( TMem
                { term_node=
                    TBinOp (op, op1, {term_node= Trange (Some t1, Some t2)}) }
            , TNoOffset ) ->
            let ty =
              match op1.term_type with Ctype t -> t | _ -> raise Unreachable
            in
            let it = self#fresh_varinfo Cil.intType "iter" in
            let env1, e_t1 = self#as_c_type Cil.intType t1 in
            let i_1 = mk_affect (Cil.var it) e_t1 in
            let env2, e_t2 = self#as_c_type Cil.intType t2 in
            let cond = cmp Rle (Cil.evar it) e_t2 in
            let env3, e_op1 = self#translate_term op1 in
            assert (env3 = Env.empty) ;
            let e = Cil.new_exp ~loc (BinOp (op, e_op1, Cil.evar it, ty)) in
            let y = (Mem e, NoOffset) in
            Cil_printer.pp_lval Format.str_formatter y ;
            let str =
              Cil.mkString t.term_loc (Format.flush_str_formatter ())
            in
            let i_f_1 = self#cnondet (Cil.typeOfLval y) y str in
            let plus_one = Cil.mkBinOp ~loc PlusA (Cil.evar it) one in
            let i_f_2 = mk_affect (Cil.var it) plus_one in
            let i_2 = Env.mk_loop cond (Env.make [] [i_f_1; i_f_2] []) in
            Env.merge env1
              (Env.merge env2 (Env.merge (Env.make [it] [i_1; i_2] []) ret))
        | TLval lv ->
            let ty =
              match t.term_type with Ctype x -> x | _ -> raise Unreachable
            in
            let env, e = self#translate_lval lv in
            Cil_printer.pp_term_lval Format.str_formatter lv ;
            let str =
              Cil.mkString t.term_loc (Format.flush_str_formatter ())
            in
            let aff = self#cnondet ty e str in
            Env.merge env (Env.merge (Env.make [] [aff] []) ret)
        | _ ->
            Options.warning ~current:true ~once:true
              "term %a in assigns clause unsupported" Printer.pp_term t ;
            ret
      in
      List.fold_left on_term Env.empty assigns_terms

    method swd_call _stmt ret_lval fct_varinfo args loc init_var =
      let kf = Globals.Functions.get fct_varinfo in
      let formals = Kernel_function.get_formals kf in
      let varname = fct_varinfo.vname ^ "_mod" in
      let new_f_vi = self#fresh_varinfo fct_varinfo.vtype varname in
      let on_bhv _ bhv env =
        let env_assumes, e_assumes = self#cond_of_assumes bhv.b_assumes in
        (* we create variables old_* to save the values of globals and
	  * formal parameters before function call *)
        let save v (a, b) =
          let d, e = self#save_varinfo kf v in
          (Env.merge d a, Env.merge e b)
        in
        let save_global v _ l = save v l in
        let save_formal l v = save v l in
        let i1, i2 =
          Globals.Vars.fold_in_file_order save_global (Env.empty, Env.empty)
        in
        let i1, i2 = List.fold_left save_formal (i1, i2) formals in
        let env_begin_save = i1 and env_end_save = i2 in
        let ensures = bhv.b_post_cond in
        let on_post env (_, {ip_content= p}) =
          let p =
            match ret_lval with
            | Some r ->
                let ty = Cil.typeOfLval r in
                result_varinfo <- Some (my_varinfo ty "__retres") ;
                Inline.pred p
            | None -> p
          in
          Env.merge env (self#pc_assume p)
        in
        let env_posts = List.fold_left on_post Env.empty ensures in
        let env_affects = self#assigns_swd [bhv.b_assigns] in
        let env_then =
          Env.merge env_begin_save
            (Env.merge env_affects (Env.merge env_posts env_end_save))
        in
        let i_bhv = Env.mk_if e_assumes env_then Env.empty in
        Env.merge env (Env.merge env_assumes (Env.make [] [i_bhv] []))
      in
      let env_body = Annotations.fold_behaviors on_bhv kf Env.empty in
      let env_before, env_after =
        match ret_lval with
        | Some r ->
            let ty = Cil.typeOfLval r in
            let retres = my_varinfo ty "__retres" in
            let str = "\\return of function '" ^ fct_varinfo.vname ^ "'" in
            let aff =
              self#cnondet ty (Cil.var retres) (Cil.mkString ~loc str)
            in
            ( Env.make [retres] [aff] []
            , Env.make [] [mk_ret (Cil.evar retres)] [] )
        | None -> (Env.empty, Env.empty)
      in
      let env = Env.merge env_before (Env.merge env_body env_after) in
      let stmts =
        List.rev_append (List.rev (Env.stmts env)) (Env.cleans env)
      in
      let locals = Env.locals env in
      let new_f = Utils.mk_fundec new_f_vi ~formals ~locals stmts in
      functions <- new_f :: functions ;
      let i_call =
        Cil.mkStmt (Instr (Call (ret_lval, Cil.evar new_f_vi, args, loc)))
      in
      let stmt = Extlib.the self#current_stmt in
      let kf = Kernel_function.find_englobing_kf stmt in
      let kf_name = Kernel_function.get_name kf in
      let init_vars =
        match init_var with None -> [] | Some init_var -> [init_var]
      in
      self#insert (Symbolic_label.beg_func kf_name) (Env.make init_vars [] []) ;
      self#insert (Symbolic_label.end_stmt stmt.sid) (Env.make [] [i_call] []) ;
      Cil.SkipChildren

    method! vstmt_aux stmt =
      let sim_funcs = Options.Simulate_Functions.get () in
      match stmt.skind with
      | Loop _ when List.mem stmt.sid swd ->
          let kf = Kernel_function.find_englobing_kf stmt in
          let ca_l = Annotations.code_annot stmt in
          let ca_l = List.map (fun x -> x.annot_content) ca_l in
          let on_bhv _ bhv env =
            let bhv_in l =
              List.mem bhv.b_name l || (Cil.is_default_behavior bhv && l = [])
            in
            let f_assigns ret = function
              | AAssigns (l, a) when bhv_in l -> a :: ret
              | _ -> ret
            in
            let f_linvs ret = function
              | AInvariant (l, _, p) when bhv_in l -> p :: ret
              | _ -> ret
            in
            let assigns = List.fold_left f_assigns [] ca_l in
            let linvs = List.fold_left f_linvs [] ca_l in
            let env_assumes, e_assumes = self#cond_of_assumes bhv.b_assumes in
            let env_affects = self#assigns_swd assigns in
            let on_inv ret p = Env.merge ret (self#pc_assume p) in
            let env_block = List.fold_left on_inv env_affects linvs in
            let i_bhv = Env.mk_if e_assumes env_block Env.empty in
            Env.merge env (Env.merge env_assumes (Env.make [] [i_bhv] []))
          in
          let env_before =
            if Annotations.behaviors kf = [] then
              on_bhv false (Cil.mk_behavior ()) Env.empty
            else Annotations.fold_behaviors on_bhv kf Env.empty
          in
          let env_after = self#pc_assume Logic_const.pfalse in
          Cil.DoChildrenPost
            (fun s ->
              self#insert (Symbolic_label.beg_stmt stmt.sid) env_before ;
              self#insert (Symbolic_label.end_iter stmt.sid) env_after ;
              s )
      | Instr
          (Call (ret, {enode= Lval (Var fct_varinfo, NoOffset)}, args, loc))
        when List.mem stmt.sid swd || List.mem fct_varinfo.vname sim_funcs ->
          self#swd_call stmt ret fct_varinfo args loc None
      | Instr (Local_init (ret, ConsInit (fct_varinfo, args, _), loc))
        when List.mem stmt.sid swd || List.mem fct_varinfo.vname sim_funcs ->
          self#swd_call stmt
            (Some (Var ret, NoOffset))
            fct_varinfo args loc (Some ret)
      | _ -> Cil.DoChildren

    method! vglob_aux =
      function
      | GVar (vi, _, _) ->
          visited_globals <- vi :: visited_globals ;
          Cil.DoChildren
      | _ -> Cil.DoChildren
  end

let translate props swd precond_fname instru_fname =
  let constraints = Input_domain.compute_constraints () in
  let gatherer = new gather_insertions props swd in
  Visitor.visitFramacFile (gatherer :> Visitor.frama_c_inplace) (Ast.get ()) ;
  let insertions = gatherer#get_insertions ()
  and functions = gatherer#get_functions ()
  and translated_props = gatherer#translated_properties ()
  and new_globals = gatherer#get_new_globals ()
  and new_init_globals = gatherer#get_new_init_globals () in
  let constraints =
    List.fold_left Input_domain.add_global constraints new_globals
  in
  let constraints =
    List.fold_left Input_domain.add_init_global constraints new_init_globals
  in
  Input_domain.translate precond_fname constraints ;
  let old_unicode = Kernel.Unicode.get () in
  Kernel.Unicode.set false ;
  let printer = new Print.print_insertions insertions functions swd in
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  printer#file fmt (Ast.get ()) ;
  let dkey = Options.dkey_generated_c in
  let out_file = open_out instru_fname in
  Options.debug ~dkey "generated C file:" ;
  if Options.is_debug_key_enabled dkey then
    Buffer.output_buffer stdout buf ;
  Buffer.output_buffer out_file buf ;
  Format.pp_print_flush fmt () ;
  flush stdout ;
  flush out_file ;
  close_out out_file ;
  Buffer.clear buf ;
  Kernel.Unicode.set old_unicode ;
  translated_props
