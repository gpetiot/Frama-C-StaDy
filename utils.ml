
let machdep() = match Kernel.Machdep.get() with
  | "x86_64" -> 64
  | "x86_32" | "ppc_32" -> 32
  | "x86_16" -> 16
  | _ -> 32


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
