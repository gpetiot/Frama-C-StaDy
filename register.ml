
open Cil_types


let typically_typer ~typing_context ~loc bhv = function
  | [p] ->
    let f = typing_context.Logic_typing.type_predicate in
    let state = typing_context.Logic_typing.pre_state in
    let pred = Logic_const.new_predicate (f state p) in
    bhv.b_extended <- ("typically", 42, [pred]) :: bhv.b_extended
  | _ ->
    typing_context.Logic_typing.error loc "predicate expected after 'typically'"

let () = Logic_typing.register_behavior_extension "typically" typically_typer


let emitter =
  Emitter.create "StaDy" [Emitter.Property_status; Emitter.Funspec]
    ~correctness:[] ~tuning:[]


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
  Utils.mpz_t_ref := mpz_t;
  List.iter (fun(a,b) -> States.Externals.add a b) externals


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
      let bhv = Utils.default_behavior kf in
      let typically_preds = Utils.typically_preds bhv in
      List.map (Property.ip_of_requires kf Kglobal bhv) typically_preds
    with _ -> []
  in
  let register p = try Property_status.register p with _ -> () in
  List.iter register strengthened_precond


let properties_of_behavior name =
  let gather p ret =
    match Property.get_behavior p with
    | Some b when b.b_name = name -> p :: ret
    | _ -> ret
  in
  Property_status.fold gather []


let properties_of_function name =
  let gather p ret =
    match Property.get_kf p with
    | Some kf when (Kernel_function.get_name kf) = name -> p :: ret
    | _ -> ret
  in
  Property_status.fold gather []


let properties_of_name name =
  let gather p ret =
    try
      let buf = Buffer.create 32 in
      let fmt = Format.formatter_of_buffer buf in
      Property.short_pretty fmt p;
      Format.pp_print_flush fmt ();
      let str = Buffer.contents buf in
      Buffer.clear buf;
      if str = name then p :: ret else ret
    with _ -> ret
  in
  Property_status.fold gather []


let selected_props() =
  let properties = Options.Properties.get () in
  let behaviors = Options.Behaviors.get () in
  let functions = Options.Functions.get () in
  let gather p b = List.rev_append (properties_of_behavior b) p in
  let props = List.fold_left gather [] behaviors in
  let gather p f = List.rev_append (properties_of_function f) p in
  let props = List.fold_left gather props functions in
  let gather p n = List.rev_append (properties_of_name n) p in
  let props = List.fold_left gather props properties in
  let app p l = p :: l in
  if props = [] then Property_status.fold app [] else props


let compute_props ?(props=selected_props()) ?swd () =
  let swd = match swd with
    | Some x -> List.map string_of_int x
    | None -> Options.SWD.get()
  in
  let valid_sid acc sid =
    try
      let sid = int_of_string sid in
      let s, _ = Kernel_function.find_from_sid sid in
      begin
	match s.skind with
	| Instr(Call _) | Loop _ -> sid :: acc
	| _ ->
	   Options.feedback ~once:true "stmt %i not a Call nor a Loop" sid;
	   acc
      end
    with _ -> Options.feedback "%s: not a valid stmt id" sid; acc
  in
  let swd = List.fold_left valid_sid [] swd in
  let files = Kernel.Files.get() in
  let fname = Filename.chop_extension (Filename.basename (List.hd files)) in
  let kf = fst (Globals.entry_point()) in
  let entry_point = Kernel_function.get_name kf in
  let precond_fname = Printf.sprintf "__sd_%s_%s.pl" fname entry_point in
  let instru_fname = Printf.sprintf "__sd_instru_%s_%s.c" fname entry_point in
  let translated_props =
    Translate.translate props swd precond_fname instru_fname in
  Test_generation.run entry_point precond_fname instru_fname;
  States.Nb_test_cases.mark_as_computed();
  States.NC_counter_examples.mark_as_computed();
  States.SW_counter_examples.mark_as_computed();
  Options.result "all-paths: %b" (States.All_Paths.get());
  Options.result "%i test cases" (States.Nb_test_cases.get());
  let strengthened_precond =
    try
      let bhv = Utils.default_behavior kf in
      let typically_preds = Utils.typically_preds bhv in
      List.map (Property.ip_of_requires kf Kglobal bhv) typically_preds
    with _ -> []
  in
  let no_CE = States.NC_counter_examples.length() = 0 in
  let on_prop prop =
    begin
      match NCCE.one_for prop with
      | Some ncce ->
	 Options.result "%a" NCCE.pretty ncce;
	 let status = Property_status.False_and_reachable in
	 Property_status.emit emitter ~hyps:[] prop ~distinct:true status
      | None ->
	 let status = Property_status.True in
	 let hyps = strengthened_precond in
	 if States.All_Paths.get() && no_CE
	    && List.mem prop translated_props then
	   Property_status.emit emitter ~hyps prop ~distinct:true status
    end;
    Extlib.may (Options.result "%a" SWCE.pretty) (SWCE.one_for prop)
  in
  Property_status.iter on_prop


let run() =
  if Options.Enabled.get() then
    begin
      setup_props_bijection();
      do_externals();
      compute_props ();
      States.Id_To_Property.clear();
      States.Property_To_Id.clear();
      States.Not_Translated_Predicates.clear();
      Utils.mpz_t_ref := None;
      States.Externals.clear()
    end


let extern_run () =
  Options.Enabled.set true;
  run ()

let extern_run = Dynamic.register ~plugin:"stady" ~journalize:true "run_stady"
  (Datatype.func Datatype.unit Datatype.unit) extern_run


let run =
  let deps = [Ast.self; Options.Enabled.self] in
  let f, _self = State_builder.apply_once "stady" deps run in
  f
    
let () = Db.Main.extend run
