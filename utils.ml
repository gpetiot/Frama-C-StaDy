
let append_end l elt = List.rev_append (List.rev l) [elt]

let no_repeat l =
  let rec aux acc = function
    | [] -> acc
    | h :: t when List.mem h acc -> aux acc t
    | h :: t -> aux (h :: acc) t
  in
  aux  [] l

let fieldinfo_to_int fi =
  let rec aux cpt = function
    | {Cil_types.forig_name=s}::_ when s = fi.Cil_types.forig_name ->
      Integer.of_int cpt
    | _::t -> aux (cpt+1) t
    | _ -> assert false
  in
  aux 0 fi.Cil_types.fcomp.Cil_types.cfields

let machdep() = match Kernel.Machdep.get() with
  | "x86_64" -> 64
  | "x86_32" | "ppc_32" -> 32
  | "x86_16" -> 16
  | _ -> 32

let default_behavior kf =
  List.find Cil.is_default_behavior (Annotations.behaviors kf)

let unguarded_behaviors kf =
  let on_bhv _emitter bhv acc =
    match bhv.Cil_types.b_assumes with [] -> bhv :: acc | _ -> acc
  in
  Annotations.fold_behaviors on_bhv kf []

let typically_preds bhv =
  let is_typically (s,_,_) = s = "typically" in
  let typically = List.filter is_typically bhv.Cil_types.b_extended in
  let typically = List.map (fun (_,_,pred) -> pred) typically in
  List.fold_left List.rev_append [] typically

let to_id = States.Property_To_Id.find
let to_prop = States.Id_To_Property.find


open Cil_types

let rec unname = function
  | TNamed (x, _) -> unname x.ttype
  | TPtr (x,y) -> TPtr (unname x, y)
  | TArray (a,_b,_c,_d) -> TPtr (unname a, _d)
  | x -> x

(* extract guards for logic vars, e.g.: [0 <= a <= 10; x <= b <= y] *)
let extract_guards var p =
  let merge x y = match (x,y) with
    | Some x, None | None, Some x -> Some x | None, None -> None
    | _ -> assert false
  in
  let rec to_guard t = match t.term_node with
    | TLogic_coerce (_, t) -> to_guard t
    | TLval(TVar x, TNoOffset) -> Cil_datatype.Logic_var.equal x var
    | _ -> false
  in
  let rec aux p = match p.content with
    | Pand(p1, p2) ->
      let a,b,c,d = aux p1 and e,f,g,h = aux p2 in
      merge a e, merge b f, merge c g, merge d h
    | Prel((Rlt|Rle) as r, t, u) when to_guard t -> None, None, Some r, Some u
    | Prel((Rlt|Rle) as r, t, u) when to_guard u -> Some t, Some r, None, None
    | Prel(Rge, t, u) when to_guard t -> Some u, Some Rle, None, None
    | Prel(Rgt, t, u) when to_guard t -> Some u, Some Rlt, None, None
    | Prel(Rge, t, u) when to_guard u -> None, None, Some Rle, Some t
    | Prel(Rgt, t, u) when to_guard u -> None, None, Some Rlt, Some t
    | _ -> None, None, None, None
  in
  let a,b,c,d = aux p in
  Extlib.the a, Extlib.the b, Extlib.the c, Extlib.the d


let error_term t = Options.abort "term: %a" Debug.pp_term t
let error_toffset t = Options.abort "toffset: %a" Debug.pp_toffset t
let error_pred p = Options.abort "pred: %a" Debug.pp_pred p

let is_one = function
  | {term_node=TConst(Integer(i,_))} when Integer.equal i Integer.one -> true
  | _ -> false


(* Extracts the varinfo of the variable and its inferred size as a term
   from a term t as \valid(t). *)
let rec extract_from_valid t =
  let loc = t.term_loc in
  match t.term_node with
  | TBinOp ((PlusPI|IndexPI|MinusPI) as op,
    	    {term_node=TCastE((TPtr _) as ty,t)},
    	    ({term_node=(Trange (_, Some _))} as operand2)) ->
    extract_from_valid
      {t with term_node=TBinOp(op, {t with term_type=Ctype ty}, operand2)}
  | TBinOp((PlusPI|IndexPI),
	   {term_node=TLval(TVar {lv_origin=Some varinfo}, _)},
	   {term_node=Trange(_,Some {term_node=TBinOp(MinusA,x,k)})})
      when is_one k ->
    varinfo, x
  | TBinOp((PlusPI|IndexPI),
	   {term_node=TLval(TVar {lv_origin=Some varinfo}, _)},
	   {term_node=Trange(_,Some bound)}) ->
    let tnode = TBinOp (PlusA, bound, Cil.lone ~loc ()) in
    let einfo = {exp_type=bound.term_type; exp_name=[]} in
    varinfo, Cil.term_of_exp_info t.term_loc tnode einfo
  | TBinOp((PlusPI|IndexPI),{term_node=TLval(TVar{lv_origin=Some vi}, _)},t2) ->
    let tnode = TBinOp (PlusA, t2, Cil.lone ~loc ()) in
    let einfo = {exp_type=t2.term_type; exp_name=[]} in
    vi, Cil.term_of_exp_info t.term_loc tnode einfo
  | TBinOp((PlusPI|IndexPI),
	   {term_node=TLval tlval},
	   {term_node=Trange(_,Some {term_node=TBinOp(MinusA,x,k)})})
      when is_one k ->
    let varinfo, _ = extract_from_valid {t with term_node=TLval tlval} in
    varinfo, x
  | TBinOp((PlusPI|IndexPI),
	   {term_node=TLval tlval},
	   {term_node=Trange(_,Some bound)}) ->
    let tnode = TBinOp (PlusA, bound, Cil.lone ~loc ()) in
    let einfo = {exp_type=bound.term_type; exp_name=[]} in
    let term = Cil.term_of_exp_info t.term_loc tnode einfo in
    let varinfo, _ = extract_from_valid {t with term_node=TLval tlval} in
    varinfo, term
  | TLval (TVar{lv_origin=Some vi},TNoOffset) -> vi, Cil.lone ~loc ()
  | TLval (TMem m, TNoOffset) ->
    let varinfo, _ = extract_from_valid m in
    varinfo, Cil.lone ~loc ()
  | TAddrOf (TMem x, TIndex (y, TNoOffset)) ->
     let x' = Cil.mkTermMem ~addr:x ~off:TNoOffset in
     let rec type_of_pointed = function
       | Ctype (TPtr (ty,_)) -> Ctype ty
       | Ctype (TArray (ty,_,_,_)) -> Ctype ty
       | Ctype (TNamed (x,_)) -> type_of_pointed (Ctype x.ttype)
       | ty ->
	  Options.abort
	    ~current:true "unsupported type %a" Printer.pp_logic_type ty
     in
     let ty = type_of_pointed (Cil.typeOfTermLval x') in
     let x' = Logic_const.term (TLval x') ty in
     extract_from_valid {t with term_node=(TBinOp(PlusPI,x',y))}
  | _ -> Options.debug "\\valid(%a)" Debug.pp_term t; assert false


(* Computes and returns a hashtable such that :
   -  var1 => inferred size for var1
   -  var2 => inferred size for var2
   -  ...
   - var n => inferred size for varn *)
let lengths_from_requires kf =
  let vi = Kernel_function.get_vi kf in
  let kf_tbl = Cil_datatype.Varinfo.Hashtbl.create 32 in
  let o = object
    inherit Visitor.frama_c_inplace

    method! vpredicate_named p =
      if List.mem "rte" p.name then Cil.SkipChildren else Cil.DoChildren

    method! vpredicate = function
    | Pvalid(_, t) | Pvalid_read(_, t) ->
      begin
	try
	  let v, term = extract_from_valid t in
	  let terms =
	    try Cil_datatype.Varinfo.Hashtbl.find kf_tbl v
	    with Not_found -> []
	  in
	  let terms = append_end terms term in
	  Cil_datatype.Varinfo.Hashtbl.replace kf_tbl v terms;
	  Cil.DoChildren
	with _ -> Cil.DoChildren
      end
    | _ -> Cil.DoChildren
  end
  in
  let on_requires p =
    let p' = Inline.id_pred p in
    ignore (Visitor.visitFramacIdPredicate o p')
  in
  let on_bhv _ bhv = List.iter on_requires bhv.b_requires in
  if not (Cil.is_unused_builtin vi) then Annotations.iter_behaviors on_bhv kf;
  kf_tbl

(* mpz_t type for GMP *)
let mpz_t_ref = ref (None:Cil_types.typ option)

let mpz_t() =
  let ty = mpz_t_ref in
  let ty = !ty in
  let ty = Extlib.the ty in
  ty


(* unused: interpreting string as precondition predicates *)
(* let type_str_precond kf pred_as_string = *)
(*   let module M = Logic_typing.Make(struct *)
(*     let is_loop() = false *)
(*     let anonCompFieldName = Cabs2cil.anonCompFieldName *)
(*     let conditionalConversion = Cabs2cil.logicConditionalConversion *)
(*     let find_macro _ = raise Not_found *)
(*     let find_var x = *)
(*       let vi = *)
(* 	try Globals.Vars.find_from_astinfo x (VLocal kf) *)
(* 	with Not_found -> *)
(* 	  try Globals.Vars.find_from_astinfo x (VFormal kf) *)
(* 	  with Not_found -> Globals.Vars.find_from_astinfo x VGlobal *)
(*       in *)
(*       Cil.cvar_to_lvar vi *)
(*     let find_enum_tag x = *)
(*       try Globals.Types.find_enum_tag x *)
(*       with Not_found -> failwith ("Unbound variable " ^ x) *)
(*     let find_type = Globals.Types.find_type *)
(*     let find_comp_field info s = Field(Cil.getCompField info s,NoOffset) *)
(*     let find_label s = Kernel_function.find_label kf s *)

(*     let remove_logic_function = Logic_env.remove_logic_function *)
(*     let remove_logic_type = Logic_env.remove_logic_type *)
(*     let remove_logic_ctor = Logic_env.remove_logic_ctor *)

(*     let add_logic_function = Logic_utils.add_logic_function *)
(*     let add_logic_type = Logic_env.add_logic_type *)
(*     let add_logic_ctor = Logic_env.add_logic_ctor *)

(*     let find_all_logic_functions = Logic_env.find_all_logic_functions *)
(*     let find_logic_type = Logic_env.find_logic_type *)
(*     let find_logic_ctor = Logic_env.find_logic_ctor *)

(*     let integral_cast ty t = *)
(*       failwith *)
(*         (Pretty_utils.sfprintf *)
(*            "term %a has type %a, but %a is expected." *)
(*            Printer.pp_term t *)
(* 	   Printer.pp_logic_type Linteger Printer.pp_typ ty) *)
(*   end) *)
(*   in *)
(*   let lenv = Logic_typing.Lenv.empty() in *)
(*   let _, lexpr = Logic_lexer.lexpr (Lexing.dummy_pos, pred_as_string) in *)
(*   M.predicate lenv lexpr *)

let binop_to_relation = function
  | Lt -> Rlt
  | Gt -> Rgt
  | Le -> Rle
  | Ge -> Rge
  | Eq -> Req
  | Ne -> Rneq
  | _ -> failwith "binop_to_relation"

let binop_to_fname = function
  | PlusA -> "add"
  | MinusA -> "sub"
  | Mult -> "mul"
  | Div -> "tdiv_q"
  | Mod -> "tdiv_r"
  | _ -> failwith "binop_to_fname"

let relation_to_binop = function
  | Rlt -> Lt
  | Rgt -> Gt
  | Rle -> Le
  | Rge -> Ge
  | Req -> Eq
  | Rneq -> Ne

let rel_to_string = function
  | Rlt -> "lt"
  | Rgt -> "gt"
  | Rle -> "le"
  | Rge -> "ge"
  | Req -> "eq"
  | Rneq -> "ne"
