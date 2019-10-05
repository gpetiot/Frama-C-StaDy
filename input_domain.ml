open Cil_types

type pl_constant = PLInt of Integer.t | PLFloat of float

type pl_term =
  | PLBinOp of pl_term * binop * pl_term
  | PLConst of pl_constant
  | PLDim of pl_term
  | PLContAll of pl_term
  | PLCont of pl_term * pl_term
  | PLLVar of logic_var
  | PLCVar of varinfo

type pl_domain =
  | PLIntDom of pl_term * Integer.t option * Integer.t option
  | PLFloatDom of pl_term * string option * string option
  | PLDoubleDom of pl_term * string option * string option

type pl_input =
  | PLIntInput of pl_term * Integer.t option * Integer.t option
  | PLFloatInput of pl_term * string option * string option
  | PLDoubleInput of pl_term * string option * string option

type pl_rel = pl_term * relation * pl_term

type pl_quantif = logic_var list * pl_rel list * pl_rel

type pl_constraint =
  | PLUnquantif of pl_rel
  | PLQuantif of pl_quantif
  | PLDomain of pl_domain
  | PLInput of pl_input

let rec is_cont = function
  | PLBinOp (x, _, y) -> is_cont x || is_cont y
  | PLConst _ -> false
  | PLDim x -> is_cont x
  | PLContAll _ -> true
  | PLCont _ -> true
  | PLLVar _ -> false
  | PLCVar _ -> false

let fieldinfo_to_int fi =
  let rec aux cpt = function
    | {Cil_types.forig_name= s} :: _ when s = fi.Cil_types.forig_name ->
        Integer.of_int cpt
    | _ :: t -> aux (cpt + 1) t
    | _ -> assert false
  in
  aux 0 fi.Cil_types.fcomp.Cil_types.cfields

let unguarded_behaviors kf =
  let on_bhv _emitter bhv acc =
    match bhv.Cil_types.b_assumes with [] -> bhv :: acc | _ -> acc
  in
  Annotations.fold_behaviors on_bhv kf []

let split_constraints constraints =
  let split (d, i, q, uq) c =
    match c with
    | PLDomain x -> (x :: d, i, q, uq)
    | PLInput x -> (d, x :: i, q, uq)
    | PLQuantif x -> (d, i, x :: q, uq)
    | PLUnquantif x -> (d, i, q, x :: uq)
  in
  List.fold_left split ([], [], [], []) constraints

let merge_constraints domains inputs quantifs unquantifs =
  let constraints = List.fold_left (fun x y -> PLDomain y :: x) [] domains in
  let constraints =
    List.fold_left (fun x y -> PLInput y :: x) constraints inputs
  in
  let constraints =
    List.fold_left (fun x y -> PLUnquantif y :: x) constraints unquantifs
  in
  List.fold_left (fun x y -> PLQuantif y :: x) constraints quantifs

class pl_printer =
  object (self)
    method constant fmt =
      function
      | PLInt i -> self#integer fmt i
      | PLFloat f -> Format.fprintf fmt "(%f0)" f

    method private is_float =
      function
      | PLConst (PLInt _) | PLDim _ -> false
      | PLConst (PLFloat _) -> true
      | PLContAll t' | PLBinOp (t', _, _) | PLCont (t', _) -> self#is_float t'
      | PLLVar lv -> Cil.isLogicFloatType lv.lv_type
      | PLCVar v -> Cil.isFloatingType v.vtype

    method binop fmt =
      function
      | PlusA | PlusPI | IndexPI -> Format.fprintf fmt "+"
      | MinusA -> Format.fprintf fmt "-"
      | Mult -> Format.fprintf fmt "*"
      | Div -> Format.fprintf fmt "/"
      | _ -> assert false

    method term fmt =
      function
      | PLBinOp (t1, b, t2) ->
          Format.fprintf fmt "%a(%s(math), %a, %a)" self#binop b
            (if self#is_float t1 then "real" else "int")
            self#term t1 self#term t2
      | PLConst c -> self#constant fmt c
      | PLDim t' -> Format.fprintf fmt "dim(%a)" self#term t'
      | PLContAll t' -> Format.fprintf fmt "cont(%a,_)" self#term t'
      | PLCont (t1, t2) ->
          Format.fprintf fmt "cont(%a,%a)" self#term t1 self#term t2
      | PLLVar lv -> Format.fprintf fmt "S_%s" lv.lv_name
      | PLCVar v -> Format.fprintf fmt "'%s'" v.vname

    method integer fmt i = Integer.pretty fmt i

    method integer_opt b fmt =
      function
      | Some i when b && Integer.compare i Integer.zero < 0 ->
          Format.fprintf fmt "(%a)" self#integer i
      | Some i -> Format.fprintf fmt "%a" self#integer i
      | None -> Format.fprintf fmt "?"

    method domain fmt =
      function
      | PLIntInput (t', Some a, Some b) when Integer.equal a b ->
          Format.fprintf fmt "%a, int([%a])" self#term t' self#integer a
      | PLIntInput (t', a, b) ->
          Format.fprintf fmt "%a, int([%a..%a])" self#term t'
            (self#integer_opt false) a (self#integer_opt true) b
      | PLFloatInput (t', str1, str2) ->
          Format.fprintf fmt "%a, float([(%s)..(%s)])" self#term t'
            (try Extlib.the str1 with _ -> "?")
            (try Extlib.the str2 with _ -> "?")
      | PLDoubleInput (t', str1, str2) ->
          Format.fprintf fmt "%a, double([(%s)..(%s)])" self#term t'
            (try Extlib.the str1 with _ -> "?")
            (try Extlib.the str2 with _ -> "?")

    method complex_domain fmt =
      function
      | PLIntDom (t', Some a, Some b) when Integer.equal a b ->
          Format.fprintf fmt "%a, [], int([%a])" self#term t' self#integer a
      | PLIntDom (t', a, b) ->
          Format.fprintf fmt "%a, [], int([%a..%a])" self#term t'
            (self#integer_opt false) a (self#integer_opt true) b
      | PLFloatDom (t', str1, str2) ->
          Format.fprintf fmt "%a, [], float([(%s)..(%s)])" self#term t'
            (try Extlib.the str1 with _ -> "?")
            (try Extlib.the str2 with _ -> "?")
      | PLDoubleDom (t', str1, str2) ->
          Format.fprintf fmt "%a, [], double([(%s)..(%s)])" self#term t'
            (try Extlib.the str1 with _ -> "?")
            (try Extlib.the str2 with _ -> "?")

    method rel fmt =
      function
      | Rlt -> Format.fprintf fmt "inf"
      | Rgt -> Format.fprintf fmt "sup"
      | Rle -> Format.fprintf fmt "infegal"
      | Rge -> Format.fprintf fmt "supegal"
      | Req -> Format.fprintf fmt "egal"
      | Rneq -> Format.fprintf fmt "diff"

    method cond fmt (x, r, y) =
      Format.fprintf fmt "cond(%a,%a,%a,pre)" self#rel r self#term x self#term
        y

    method quantif fmt (lvars, compo_rels, (x, r, y)) =
      let aux fmt s = Format.fprintf fmt "    S_%s" s.lv_name in
      Format.fprintf fmt
        "uq_cond(\n  [\n%a\n  ],\n  [\n%a\n  ],\n  %a,%a,%a)"
        (Debug.pp_list ~sep:",\n" aux)
        lvars
        (Debug.pp_list ~sep:",\n" self#cond)
        compo_rels self#rel r self#term x self#term y
  end

let prolog_header =
  ":- module(test_parameters).\n"
  ^ ":- import create_input_val/3 from substitution.\n" ^ ":- export dom/4.\n"
  ^ ":- export create_input_vals/2.\n" ^ ":- export unquantif_preconds/2.\n"
  ^ ":- export quantif_preconds/2.\n" ^ ":- export strategy/2.\n"
  ^ ":- export precondition_of/2.\n\n" ^ "dom(0,0,0,0).\n"

class to_pl =
  object (self)
    method logic_var lv =
      match lv.lv_origin with None -> PLLVar lv | Some v -> PLCVar v

    method term_offset ret =
      function
      | TNoOffset -> List.rev ret
      | TField (fi, tof) ->
          let i = PLConst (PLInt (fieldinfo_to_int fi)) in
          self#term_offset (i :: ret) tof
      | TModel _ as t -> Utils.error_toffset t
      | TIndex (t, tof) -> self#term_offset (self#term t :: ret) tof

    method term_lhost =
      function
      | TVar v -> self#logic_var v
      | TResult _ -> assert false
      | TMem {term_node= TBinOp ((PlusPI | IndexPI), x, y)} ->
          PLCont (self#term x, self#term y)
      | TMem m -> PLCont (self#term m, PLConst (PLInt Integer.zero))

    method term_lval (tlhost, toffset) =
      let tlhost' = self#term_lhost tlhost in
      let toffsets = self#term_offset [] toffset in
      List.fold_left (fun t tof -> PLCont (t, tof)) tlhost' toffsets

    method term t =
      match t.term_node with
      | TLogic_coerce (_, t') -> self#term t'
      | TConst (LEnum {eival= {enode= Const (CInt64 (ii, _, _))}})
       |TConst (Integer (ii, _)) ->
          PLConst (PLInt ii)
      | TConst (LEnum {eival= {enode= Const (CReal (f, _, _))}})
       |TConst (LReal {r_nearest= f}) ->
          PLConst (PLFloat f)
      | TConst (LEnum {eival= {enode= Const (CChr c)}}) | TConst (LChr c) ->
          PLConst (PLInt (Integer.of_int (int_of_char c)))
      | TLval tl -> self#term_lval tl
      | TBinOp (op, x, y) -> PLBinOp (self#term x, op, self#term y)
      | TUnOp (Neg, term) -> (
        match self#term term with
        | PLConst (PLInt i) -> PLConst (PLInt (Integer.neg i))
        | _ -> Utils.error_term t )
      | Tat (t', BuiltinLabel (Here | Old | Pre)) -> self#term t'
      | _ -> Utils.error_term t
  end

let term_to_pl t = try (new to_pl)#term t with _ -> Utils.error_term t

let maxuint = Cil.max_unsigned_number (Utils.machdep ())

let maxint = Cil.max_signed_number (Utils.machdep ())

let minint = Cil.min_signed_number (Utils.machdep ())

let ibounds = function
  | IBool -> (Integer.zero, Integer.one)
  | IChar | ISChar -> (Integer.of_int (-128), Integer.of_int 127)
  | IUChar -> (Integer.zero, Integer.of_int 255)
  | ik when Cil.isSigned ik -> (minint, maxint)
  | _ -> (Integer.zero, maxuint)

let float_bounds = ("-3.40282347e+38", "3.40282347e+38")

let double_bounds = ("-1.7976931348623157e+308", "1.7976931348623157e+308")

let _long_double_bounds =
  ("-1.7976931348623157e+308", "1.7976931348623157e+308")

(******* constraints creation ******)

let rec input_from_type known_structs constraints ty t is_cont =
  match Cil.unrollType ty with
  | TVoid _ ->
      if is_cont then
        PLDomain (PLIntDom (t, Some minint, Some maxint)) :: constraints
      else PLInput (PLIntInput (t, Some minint, Some maxint)) :: constraints
  | TEnum ({ekind= ik}, _) | TInt (ik, _) ->
      let b_min, b_max = ibounds ik in
      if is_cont then
        PLDomain (PLIntDom (t, Some b_min, Some b_max)) :: constraints
      else PLInput (PLIntInput (t, Some b_min, Some b_max)) :: constraints
  | TFloat (fk, _) -> (
      if is_cont then
        match fk with
        | FFloat ->
            let b_min, b_max = float_bounds in
            PLDomain (PLFloatDom (t, Some b_min, Some b_max)) :: constraints
        | FDouble ->
            let b_min, b_max = double_bounds in
            PLDomain (PLDoubleDom (t, Some b_min, Some b_max)) :: constraints
        | FLongDouble -> assert false
      else
        match fk with
        | FFloat ->
            let b_min, b_max = float_bounds in
            PLInput (PLFloatInput (t, Some b_min, Some b_max)) :: constraints
        | FDouble ->
            let b_min, b_max = double_bounds in
            PLInput (PLDoubleInput (t, Some b_min, Some b_max)) :: constraints
        | FLongDouble -> assert false )
  | TComp (ci, _, _) ->
    if Cil_datatype.Compinfo.Set.mem ci known_structs then constraints
    else begin
      let known_structs = Cil_datatype.Compinfo.Set.add ci known_structs in
      input_from_fields known_structs constraints Integer.zero t ci.cfields
    end
  | TPtr (ty', _) ->
      let d =
        if is_cont then
          PLDomain (PLIntDom (PLDim t, Some Integer.zero, Some maxuint))
        else PLInput (PLIntInput (PLDim t, Some Integer.zero, Some maxuint))
      in
      input_from_type known_structs (d :: constraints) ty' (PLContAll t) true
  | TArray (ty', _, _, _) ->
      (* attribute "arraylen" may contain the static size of the array but we do
      * not need it for the precondition *)
      input_from_type known_structs constraints ty' (PLContAll t) true
  | _ ->
      Options.warning ~current:true "unsupported input_from_type (%a) (%a)"
        Printer.pp_typ ty (new pl_printer)#term t ;
      constraints

and input_from_fields known_structs constraints i t = function
  | [] -> constraints
  | f :: fields ->
      let d =
        input_from_type known_structs constraints f.ftype
          (PLCont (t, PLConst (PLInt i)))
          true
      in
      input_from_fields known_structs d (Integer.succ i) t fields

let input_from_type constraints i t =
  input_from_type Cil_datatype.Compinfo.Set.empty constraints i t

let rec valid_to_prolog term =
  let maxuint = Cil.max_unsigned_number (Utils.machdep ()) in
  match term.term_node with
  | TLval _ ->
      let t = term_to_pl term in
      if is_cont t then
        [PLDomain (PLIntDom (PLDim t, Some Integer.one, Some maxuint))]
      else [PLInput (PLIntInput (PLDim t, Some Integer.one, Some maxuint))]
  | TAddrOf (TMem x, TIndex (y, TNoOffset)) ->
      let x' = Cil.mkTermMem ~addr:x ~off:TNoOffset in
      let rec type_of_pointed = function
        | Ctype (TPtr (ty, _)) -> Ctype ty
        | Ctype (TArray (ty, _, _, _)) -> Ctype ty
        | Ctype (TNamed (x, _)) -> type_of_pointed (Ctype x.ttype)
        | ty ->
            Options.abort ~current:true "unsupported type %a"
              Printer.pp_logic_type ty
      in
      let ty = type_of_pointed (Cil.typeOfTermLval x') in
      let x' = Logic_const.term (TLval x') ty in
      valid_to_prolog {term with term_node= TBinOp (PlusPI, x', y)}
  | TBinOp
      ( ((PlusPI | IndexPI | MinusPI) as op)
      , {term_node= TCastE ((TPtr _ as ty), t)}
      , ({term_node= Trange (_, Some _)} as operand2) ) ->
      valid_to_prolog
        { term with
          term_node= TBinOp (op, {t with term_type= Ctype ty}, operand2) }
  | TBinOp ((PlusPI | IndexPI), t, {term_node= Trange (_, Some x)}) -> (
      let t' = term_to_pl t in
      let x' = term_to_pl x in
      let one = PLConst (PLInt Integer.one) in
      match x' with
      | PLConst (PLInt i) ->
          let i' = Integer.add i Integer.one in
          if is_cont t' then
            [PLDomain (PLIntDom (PLDim t', Some i', Some maxuint))]
          else [PLInput (PLIntInput (PLDim t', Some i', Some maxuint))]
      | _ ->
          [ PLInput (PLIntInput (PLDim t', Some Integer.zero, Some maxuint))
          ; PLUnquantif (PLDim t', Req, PLBinOp (x', PlusA, one)) ] )
  | _ -> Utils.error_term term

let rel_to_prolog rel term1 term2 =
  let var1 = term_to_pl term1 in
  let var2 = term_to_pl term2 in
  PLUnquantif (var1, rel, var2)

let rec requires_to_prolog constraints pred =
  match pred.pred_content with
  | Pand (p, q) -> requires_to_prolog (requires_to_prolog constraints p) q
  | Ptrue -> constraints
  | Pvalid (_, t) | Pvalid_read (_, t) ->
      List.rev_append (valid_to_prolog t) constraints
  | Prel (rel, pn1, pn2) -> rel_to_prolog rel pn1 pn2 :: constraints
  | Pat (p, BuiltinLabel Here) -> requires_to_prolog constraints p
  | _ -> assert false

let merge_inputs inputs unquantifs =
  let domains_tbl = Hashtbl.create 32 in
  let is_int_domain = function PLIntInput _ -> true | _ -> false in
  let int_doms, float_doms = List.partition is_int_domain inputs in
  let merge_int f a b =
    match (a, b) with
    | None, x -> x
    | x, None -> x
    | Some x, Some y -> Some (f x y)
  in
  let merge_int_doms = function
    | PLIntInput (t, i1, i2) -> (
      try
        let lower, upper = Hashtbl.find domains_tbl t in
        let lower' = merge_int Integer.max lower i1 in
        let upper' = merge_int Integer.min upper i2 in
        Hashtbl.replace domains_tbl t (lower', upper')
      with _ -> Hashtbl.add domains_tbl t (i1, i2) )
    | _ -> assert false
  in
  List.iter merge_int_doms int_doms ;
  let extract_ops t =
    let rec aux f = function
      | PLCVar _ as t -> (t, f)
      | PLBinOp (a, PlusA, PLConst (PLInt b)) ->
          aux (fun x -> Integer.add x b) a
      | PLBinOp (a, MinusA, PLConst (PLInt b)) ->
          aux (fun x -> Integer.sub x b) a
      | PLBinOp (a, Mult, PLConst (PLInt b)) ->
          aux (fun x -> Integer.mul x b) a
      | _ -> assert false
    in
    aux Extlib.id t
  in
  let fixed_dims, unquantifs =
    let rec aux ret1 ret2 = function
      | ((PLDim t1, Req, t2) as unquantif) :: t -> (
        try
          let t', to_apply = extract_ops t2 in
          let x, y = Hashtbl.find domains_tbl t' in
          let x = to_apply (Extlib.the x) in
          let y = to_apply (Extlib.the y) in
          if not (Integer.equal x y) then assert false ;
          let x = Integer.succ x and y = Integer.succ y in
          let dom = PLIntInput (PLDim t1, Some x, Some y) in
          aux (dom :: ret1) ret2 t
        with _ -> aux ret1 (unquantif :: ret2) t )
      | unquantif :: t -> aux ret1 (unquantif :: ret2) t
      | [] -> (ret1, ret2)
    in
    aux [] [] unquantifs
  in
  List.iter merge_int_doms fixed_dims ;
  let add_int_dom_to_list k (v, w) doms = PLIntInput (k, v, w) :: doms in
  (Hashtbl.fold add_int_dom_to_list domains_tbl float_doms, unquantifs)

let compute_constraints () =
  let kf = fst (Globals.entry_point ()) in
  let bhvs = unguarded_behaviors kf in
  let accumulate f =
    List.fold_left (fun l x -> List.rev_append (f x) l) [] bhvs
  in
  let requires_preds = accumulate (fun x -> x.b_requires) in
  let typically_preds = accumulate Utils.typically_preds in
  let f constraints id_pred =
    let pnamed = Logic_const.pred_of_id_pred id_pred in
    let pnamed = Inline.pred pnamed in
    try requires_to_prolog constraints pnamed with _ ->
      Options.debug ~current:true ~once:true ~level:2
        "Native Precondition:@\n%a unsupported" Printer.pp_predicate pnamed ;
      (* this predicate has not been translated in Prolog, we must translate it
	 in C. *)
      States.Not_Translated_Predicates.add id_pred.ip_id ;
      constraints
  in
  let constraints = List.fold_left f [] typically_preds in
  let constraints = List.fold_left f constraints requires_preds in
  let formals = Kernel_function.get_formals kf in
  let create_input d v = input_from_type d v.vtype (PLCVar v) false in
  let constraints = List.fold_left create_input constraints formals in
  let constraints =
    Globals.Vars.fold_in_file_order (fun v _ d -> create_input d v) constraints
  in
  let domains, inputs, quantifs, unquantifs = split_constraints constraints in
  let inputs, unquantifs = merge_inputs inputs unquantifs in
  let constraints = merge_constraints domains inputs quantifs unquantifs in
  constraints

let add_global constraints v =
  input_from_type constraints v.vtype (PLCVar v) false

let add_init_global constraints v =
  match Utils.unname v.vtype with
  | TInt _ ->
      PLDomain (PLIntDom (PLCVar v, Some Integer.zero, Some Integer.zero))
      :: constraints
  | _ -> assert false

let translate precond_file_name constraints =
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  let kf = fst (Globals.entry_point ()) in
  let func_name = Kernel_function.get_name kf in
  let precond_name = "pathcrawler__" ^ func_name ^ "_precond" in
  let domains, inputs, quantifs, unquantifs = split_constraints constraints in
  let same_constraint_for_precond before after =
    Format.fprintf fmt "%s('%s',%s) :-\n  %s('%s',%s).\n" before precond_name
      after before func_name after
  in
  let printer = new pl_printer in
  (* PRINTING *)
  Format.fprintf fmt "%s" prolog_header ;
  let on_complex_domain x =
    Format.fprintf fmt "dom('%s', %a).\n" func_name printer#complex_domain x
  in
  List.iter on_complex_domain domains ;
  same_constraint_for_precond "dom" "A,B,C" ;
  Format.fprintf fmt "create_input_vals('%s', Ins):-\n" func_name ;
  let on_simple_domain x =
    Format.fprintf fmt "  create_input_val(%a,Ins),\n" printer#domain x
  in
  List.iter on_simple_domain inputs ;
  Format.fprintf fmt "  true.\n" ;
  same_constraint_for_precond "create_input_vals" "Ins" ;
  let pp_quantif fmt k = Format.fprintf fmt "    %a" printer#quantif k in
  let pp_unquantif fmt k = Format.fprintf fmt "    %a" printer#cond k in
  Format.fprintf fmt "quantif_preconds('%s',\n  [\n%a\n  ]\n).\n" func_name
    (Debug.pp_list ~sep:"," pp_quantif)
    quantifs ;
  same_constraint_for_precond "quantif_preconds" "A" ;
  Format.fprintf fmt "unquantif_preconds('%s',\n  [\n%a\n  ]\n).\n" func_name
    (Debug.pp_list ~sep:"," pp_unquantif)
    unquantifs ;
  same_constraint_for_precond "unquantif_preconds" "A" ;
  Format.fprintf fmt "strategy('%s',[]).\n" func_name ;
  same_constraint_for_precond "strategy" "A" ;
  Format.fprintf fmt "precondition_of('%s','%s').\n" func_name precond_name ;
  (* END OF PRINTING *)
  let dkey = Options.dkey_generated_pl in
  let out_file = open_out precond_file_name in
  Options.debug ~dkey "generated Prolog precondition:" ;
  if Options.is_debug_key_enabled dkey then
    Buffer.output_buffer stdout buf ;
  Buffer.output_buffer out_file buf ;
  Format.pp_print_flush fmt () ;
  flush stdout ;
  flush out_file ;
  close_out out_file ;
  Buffer.clear buf
