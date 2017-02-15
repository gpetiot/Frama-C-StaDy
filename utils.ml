
let machdep() = match Kernel.Machdep.get() with
  | "x86_64" -> 64
  | "x86_32" | "ppc_32" -> 32
  | "x86_16" -> 16
  | _ -> 32

let to_id = States.Property_To_Id.find
let to_prop = States.Id_To_Property.find
let get_var_desc s =
  if States.Var_Descriptions.mem s then
    let s' = States.Var_Descriptions.find s in
    if s' = "" then s else s'
  else s


open Cil_types

(* interpreting string as precondition predicates *)
let type_str_precond kf pred_as_string =
  let module M = Logic_typing.Make(struct
    let is_loop() = false
    let anonCompFieldName = Cabs2cil.anonCompFieldName
    let conditionalConversion = Cabs2cil.logicConditionalConversion
    let find_macro _ = raise Not_found
    let find_var x =
      let vi =
	try Globals.Vars.find_from_astinfo x (VLocal kf)
	with Not_found ->
	  try Globals.Vars.find_from_astinfo x (VFormal kf)
	  with Not_found -> Globals.Vars.find_from_astinfo x VGlobal
      in
      Cil.cvar_to_lvar vi
    let find_enum_tag x =
      try Globals.Types.find_enum_tag x
      with Not_found -> failwith ("Unbound variable " ^ x)
    let find_type = Globals.Types.find_type
    let find_comp_field info s = Field(Cil.getCompField info s,NoOffset)
    let find_label s = Kernel_function.find_label kf s
    let remove_logic_function = Logic_env.remove_logic_function
    let remove_logic_type = Logic_env.remove_logic_type
    let remove_logic_ctor = Logic_env.remove_logic_ctor
    let add_logic_function = Logic_utils.add_logic_function
    let add_logic_type = Logic_env.add_logic_type
    let add_logic_ctor = Logic_env.add_logic_ctor
    let find_all_logic_functions = Logic_env.find_all_logic_functions
    let find_logic_type = Logic_env.find_logic_type
    let find_logic_ctor = Logic_env.find_logic_ctor
    let integral_cast ty t =
      failwith
        (Pretty_utils.sfprintf
           "term %a has type %a, but %a is expected."
           Printer.pp_term t
	   Printer.pp_logic_type Linteger Printer.pp_typ ty)
    exception Error of Cil_types.location * string
    let error loc = Pretty_utils.ksfprintf (fun e -> raise (Error (loc, e)))
  end)
  in
  let lenv = Logic_typing.Lenv.empty() in
  let _, lexpr = Logic_lexer.lexpr (Lexing.dummy_pos, pred_as_string) in
  M.predicate lenv lexpr
    
let typically_preds_memo = ref []
let typically_preds_computed = ref false

let typically_preds bhv =
  if !typically_preds_computed then
    !typically_preds_memo
  else
    let is_typically (str, kind) = match kind with
      | Ext_preds _ -> str = "typically"
      | _ -> false
    in
    let typically = List.filter is_typically bhv.Cil_types.b_extended in
    let typically = List.map (fun (_,Ext_preds pred) -> pred) typically in
    let typically = List.fold_left List.rev_append [] typically in
    let typically =
      if not (Options.Precondition.is_default()) then
	try
	  let kf = fst (Globals.entry_point()) in
	  (type_str_precond kf (Options.Precondition.get())) :: typically
	with _ -> typically
      else typically
    in
    typically_preds_memo := List.map Logic_const.new_predicate typically;
    typically_preds_computed := true;
    !typically_preds_memo

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
  let rec aux p = match p.pred_content with
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

let relation_to_string = function
  | Rlt -> "lt"
  | Rgt -> "gt"
  | Rle -> "le"
  | Rge -> "ge"
  | Req -> "eq"
  | Rneq -> "ne"

let do_externals() =
  States.Externals.clear();
  let p' = Project.create "__stady_externals"  in
  let mpz_t, externals = Project.on p' (fun () ->
    let old_verbose = Kernel.Verbose.get() in
    Kernel.GeneralVerbose.set 0;
    let file = Options.Share.file ~error:true "externals.c" in
    let mpz_t_file = File.from_filename file in
    File.init_from_c_files [mpz_t_file];
    let tmp_mpz_t = ref None in
    let externals = ref [] in
    let set_mpzt = object
      inherit Cil.nopCilVisitor
      method !vglob = function
      | GType({ torig_name = "mpz_t" } as info, _) ->
	tmp_mpz_t := Some (TNamed(info,[]));
	Cil.SkipChildren
      | GFun({svar=vi},_) ->
	externals := (vi.vname, vi) :: !externals;
	Cil.SkipChildren
      | _ -> Cil.SkipChildren
    end in
    Cil.visitCilFileSameGlobals set_mpzt (Ast.get ());
    Kernel.GeneralVerbose.set old_verbose;
    !tmp_mpz_t, !externals
  ) () in
  Project.remove ~project:p' ();
  mpz_t_ref := mpz_t;
  List.iter (fun(a,b) -> States.Externals.add a b) externals

let default_behavior kf =
  List.find Cil.is_default_behavior (Annotations.behaviors kf)

let setup_props_bijection () =
  States.Id_To_Property.clear();
  States.Property_To_Id.clear();
  (* Bijection: unique_identifier <--> property *)
  let property_id = ref 0 in
  let fc_builtin = "__fc_builtin_for_normalization.i" in
  let on_property property =
    let pos1,_ = Property.location property in
    if (Filename.basename pos1.Lexing.pos_fname) <> fc_builtin then
      begin
	States.Property_To_Id.add property !property_id;
	States.Id_To_Property.add !property_id property;
	property_id := !property_id + 1
      end
  in
  Property_status.iter on_property;
  let kf = fst (Globals.entry_point()) in
  let strengthened_precond =
    try
      let bhv = default_behavior kf in
      let typically_preds = typically_preds bhv in
      List.map (Property.ip_of_requires kf Kglobal bhv) typically_preds
    with _ -> []
  in
  let register p = try Property_status.register p with _ -> () in
  List.iter register strengthened_precond

let initialize() =
  setup_props_bijection();
  do_externals()

let finalize() =
  States.Id_To_Property.clear();
  States.Property_To_Id.clear();
  States.Not_Translated_Predicates.clear();
  mpz_t_ref := None;
  States.Externals.clear();
  States.Var_Descriptions.clear();
  Options.PathCrawler_Options.clear();
  Options.Socket_Type.clear();
  Options.Timeout.clear();
  Options.Stop_When_Assert_Violated.clear();
  Options.Functions.clear();
  Options.Behaviors.clear();
  Options.Properties.clear();
  Options.SWD.clear();
  Options.Precondition.clear();
  Options.Simulate_Functions.clear()
