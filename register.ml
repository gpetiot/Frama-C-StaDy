
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


let translate props cwd =
  let gatherer = new Insertions.gather_insertions props cwd in
  Visitor.visitFramacFile (gatherer :> Visitor.frama_c_inplace) (Ast.get());
  let insertions = gatherer#get_insertions()
  and functions = gatherer#get_functions()
  and props = gatherer#translated_properties()
  and globals = gatherer#get_new_globals()
  and init_globals = gatherer#get_new_init_globals() in
  let print_insertions_at_label lab insertions =
    let dkey = Options.dkey_insertions in
    let f ins =
      Options.Self.feedback ~dkey "/* %a */ %a"
	Print.pp_label lab Print.pp_insertion_lb ins
    in
    Queue.iter f insertions;
    Options.Self.feedback ~dkey "--------------------"
  in
  Hashtbl.iter print_insertions_at_label insertions;
  insertions, functions, props, globals, init_globals


let print_translation filename insertions fcts cwd =
  let old_unicode = Kernel.Unicode.get() in
  Kernel.Unicode.set false;
  let printer = new Print.print_insertions insertions fcts cwd () in
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  printer#file fmt (Ast.get());
  let dkey = Options.dkey_generated_c in
  let out_file = open_out filename in
  Options.Self.debug ~dkey "generated C file:";
  let dkeys = Options.Self.Debug_category.get() in
  if Datatype.String.Set.mem "generated-c" dkeys then
    Buffer.output_buffer stdout buf;
  Buffer.output_buffer out_file buf;
  Format.pp_print_flush fmt();
  flush stdout;
  flush out_file;
  close_out out_file;
  Buffer.clear buf;
  Kernel.Unicode.set old_unicode


let emitter =
  Emitter.create "StaDy" [Emitter.Property_status; Emitter.Funspec]
    ~correctness:[] ~tuning:[]


let do_externals() =
  States.Externals.clear();
  let p' = Project.create "__stady_externals"  in
  let mpz_t, externals = Project.on p' (fun () ->
    let old_verbose = Kernel.Verbose.get() in
    Kernel.GeneralVerbose.set 0;
    let file = Options.Self.Share.file ~error:true "externals.c" in
    let mpz_t_file = File.from_filename file in
    File.init_from_c_files [mpz_t_file];
    let tmp_mpz_t = ref None in
    let externals = ref [] in
    let set_mpzt = object
      inherit Cil.nopCilVisitor
      method !vglob = function
      | GType({ torig_name = s } as info, _) when s = "mpz_t" ->
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
  Options.mpz_t := mpz_t;
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


let compute_props ?(props=selected_props()) ?cwd () =
  let cwd = match cwd with
    | Some x -> Some x
    | None when Options.CWD.get() = -500 (* default value *) -> None
    | None ->
      let sid = Options.CWD.get() in
      try let stmt, _ = Kernel_function.find_from_sid sid in Some stmt
      with _ -> Options.Self.feedback ~once:true "stmt %i not found" sid; None
  in
  let cwd = match cwd with
    | Some {skind=Instr(Call _)|Loop _} -> cwd
    | Some x ->
       Options.Self.feedback ~once:true "stmt %i not a Call nor a Loop" x.sid;
       None
    | None -> None
  in
  let files = Kernel.Files.get() in
  let fname = Filename.chop_extension (Filename.basename (List.hd files)) in
  let kf = fst (Globals.entry_point()) in
  let entry_point = Kernel_function.get_name kf in
  let precond_fname = Printf.sprintf "__sd_%s_%s.pl" fname entry_point in
  let instru_fname = Printf.sprintf "__sd_instru_%s_%s.c" fname entry_point in
  (* Translate some parts of the pre-condition in Prolog *)
  let native_precond_generated, domains, unquantifs, quantifs =
    try let a,b,c = Native_precond.compute_constraints() in true, a, b, c
    with _ -> false, [], [], []
  in
  Options.Self.feedback ~dkey:Options.dkey_native_precond
    "Prolog pre-condition %s generated"
    (if native_precond_generated then "successfully" else "not");
  let insertions, functions, translated_props, new_globals, new_init_globals =
    translate props cwd in
  let test_params =
    if native_precond_generated || new_globals <> [] ||
	 new_init_globals <> [] then
      begin
	let add_global = Native_precond.add_global in
	let add_init_global = Native_precond.add_init_global in 
	let domains = List.fold_left add_global domains new_globals in
	let domains = List.fold_left add_init_global domains new_init_globals in
	Native_precond.translate precond_fname domains unquantifs quantifs;
	Printf.sprintf "-pc-test-params %s" precond_fname
      end
    else ""
  in
  print_translation instru_fname insertions functions cwd;
  let stop_when_assert_violated =
    if Options.Stop_When_Assert_Violated.get() then
      "-pc-stop-when-assert-violated"
    else ""
  in
  let cmd =
    Printf.sprintf
      "frama-c -add-path /usr/local/lib/frama-c/plugins %s -main %s -lib-entry \
       -pc -pc-gmp -pc-validate-asserts %s -pc-com %s -pc-no-xml %s -pc-deter \
       -pc-session-timeout=%i %s"
      instru_fname
      entry_point
      test_params
      (Options.Socket_Type.get())
      (Options.PathCrawler_Options.get())
      (Options.Timeout.get())
      stop_when_assert_violated
  in
  Options.Self.debug ~dkey:Options.dkey_socket "cmd: %s" cmd;
  (* open socket with the generator *)
  begin
    match Options.Socket_Type.get() with
    | s when s = "unix" ->
      let socket = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
      let name = "Pc2FcSocket" in
      begin
	try
	  Unix.bind socket (Unix.ADDR_UNIX name);
	  Unix.listen socket 2;
	  let ret = Unix.system cmd in
	  let rec aux cpt =
	    if cpt < 3 then
	      let client, _ = Unix.accept socket in
	      Socket.process_socket client;
	      Socket.print_exit_code ret;
	      aux (cpt+1)
	  in
	  aux 0
	with _ ->
	  Unix.close socket;
	  Options.Self.abort "unix socket now closed!"
      end;
      Unix.close socket;
      Sys.remove name
    | s when s = "internet" ->
      let socket = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
      begin
	try
	  Unix.bind socket(Unix.ADDR_INET(Unix.inet_addr_loopback,2222));
	  Unix.listen socket 2;
	  let ret = Unix.system cmd in
	  let rec aux cpt =
	    if cpt < 3 then
              let client, _ = Unix.accept socket in
	      Socket.process_socket client;
	      Socket.print_exit_code ret;
	      aux (cpt+1)
	  in
	  aux 0
	with _ ->
	  Unix.close socket;
	  Options.Self.abort "internet socket now closed!"
      end;
      Unix.close socket
    | _ (* stdio *) ->
      let chan = Unix.open_process_in cmd in
      Socket.process_channel chan;
      let ret = Unix.close_process_in chan in
      Socket.print_exit_code ret
  end;
  States.Nb_test_cases.mark_as_computed();
  States.NC_counter_examples.mark_as_computed();
  States.CW_counter_examples.mark_as_computed();
  Options.Self.result "all-paths: %b" (States.All_Paths.get());
  Options.Self.result "%i test cases" (States.Nb_test_cases.get());
  let distinct = true in
  let strengthened_precond =
    try
      let bhv = Utils.default_behavior kf in
      let typically_preds = Utils.typically_preds bhv in
      List.map (Property.ip_of_requires kf Kglobal bhv) typically_preds
    with _ -> []
  in
  let no_CE = States.NC_counter_examples.length() = 0 in
  let on_prop prop =
    Options.Self.result "%a" Utils.pp_ce prop;
    try
      ignore (States.NC_counter_examples.find prop);
      let status = Property_status.False_and_reachable in
      Property_status.emit emitter ~hyps:[] prop ~distinct status
    with
    | Not_found ->
      let status = Property_status.True in
      let hyps = strengthened_precond in
      if States.All_Paths.get() && no_CE && List.mem prop translated_props then
	Property_status.emit emitter ~hyps prop ~distinct status
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
      Options.mpz_t := None;
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
