
open Cil_types


let typically_typer ~typing_context ~loc bhv = function
  | p::[] ->
    let f = typing_context.Logic_typing.type_predicate in
    let state = typing_context.Logic_typing.pre_state in
    let pred = Logic_const.new_predicate (f state p) in
    bhv.b_extended <- ("typically", 42, [pred]) ::bhv.b_extended
  | _ -> typing_context.Logic_typing.error loc
    "expecting a predicate after keyword 'typically'"

let () = Logic_typing.register_behavior_extension "typically" typically_typer


let translate props spec_insuf =
  let gatherer = new Sd_insertions.gather_insertions props spec_insuf in
  Visitor.visitFramacFile (gatherer :> Visitor.frama_c_inplace) (Ast.get());
  let insertions = gatherer#get_insertions() in
  let print_insertions_at_label lab insertions =
    let dkey = Sd_options.dkey_insertions in
    let f ins =
      Sd_options.Self.feedback ~dkey "/* %a */ %a"
	Sd_print.pp_label lab Sd_print.pp_insertion_lb ins
    in
    Queue.iter f insertions;
    Sd_options.Self.feedback ~dkey "--------------------"
  in
  Hashtbl.iter print_insertions_at_label insertions;
  insertions, gatherer#translated_properties(), gatherer#get_new_globals()


let print_translation filename insertions spec_insuf =
  let old_unicode = Kernel.Unicode.get() in
  Kernel.Unicode.set false;
  let printer = new Sd_print.print_insertions insertions spec_insuf () in
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  printer#file fmt (Ast.get());
  let dkey = Sd_options.dkey_generated_c in
  let out_file = open_out filename in
  Sd_options.Self.debug ~dkey "generated C file:";
  let dkeys = Sd_options.Self.Debug_category.get() in
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
  Sd_states.Externals.clear();
  let p' = Project.create "__stady_externals"  in
  let mpz_t, externals = Project.on p' (fun () ->
    let old_verbose = Kernel.Verbose.get() in
    Kernel.GeneralVerbose.set 0;
    let file = Sd_options.Self.Share.file ~error:true "externals.c" in
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
  Sd_options.mpz_t := mpz_t;
  List.iter (fun(a,b) -> Sd_states.Externals.add a b) externals


let setup_props_bijection () =
  Sd_states.Id_To_Property.clear();
  Sd_states.Property_To_Id.clear();
  (* Bijection: unique_identifier <--> property *)
  let property_id = ref 0 in
  let fc_builtin = "__fc_builtin_for_normalization.i" in
  let on_property property =
    let pos1,_ = Property.location property in
    if (Filename.basename pos1.Lexing.pos_fname) <> fc_builtin then
      begin
	Sd_states.Property_To_Id.add property !property_id;
	Sd_states.Id_To_Property.add !property_id property;
	property_id := !property_id + 1
      end
  in
  Property_status.iter on_property;
  let kf = fst (Globals.entry_point()) in
  let strengthened_precond =
    try
      let bhv = Sd_utils.default_behavior kf in
      let typically_preds = Sd_utils.typically_preds bhv in
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
  let properties = Sd_options.Properties.get () in
  let behaviors = Sd_options.Behaviors.get () in
  let functions = Sd_options.Functions.get () in
  let gather p b = List.rev_append (properties_of_behavior b) p in
  let props = List.fold_left gather [] behaviors in
  let gather p f = List.rev_append (properties_of_function f) p in
  let props = List.fold_left gather props functions in
  let gather p n = List.rev_append (properties_of_name n) p in
  let props = List.fold_left gather props properties in
  let app p l = p :: l in
  if props = [] then Property_status.fold app [] else props


let compute_props ?(props=selected_props()) ?spec_insuf () =
  let spec_insuf =
    match spec_insuf with
    | Some x -> Some x
    | None ->
      let sid = Sd_options.Spec_Insuf.get() in
      try let stmt, _ = Kernel_function.find_from_sid sid in Some stmt
      with _ -> None
  in
  let files = Kernel.Files.get() in
  let fname = Filename.chop_extension (Filename.basename (List.hd files)) in
  let kf = fst (Globals.entry_point()) in
  let entry_point = Kernel_function.get_name kf in
  let precond_fname = Printf.sprintf "__sd_%s_%s.pl" fname entry_point in
  let instru_fname = Printf.sprintf "__sd_instru_%s_%s.c" fname entry_point in
  (* Translate some parts of the pre-condition in Prolog *)
  let native_precond_generated, domains, unquantifs, quantifs =
    try let a,b,c = Sd_native_precond.compute_constraints() in true, a, b, c
    with _ -> false, [], [], []
  in
  Sd_options.Self.feedback ~dkey:Sd_options.dkey_native_precond
    "Prolog pre-condition %s generated"
    (if native_precond_generated then "successfully" else "not");
  let insertions, translated_props, new_globals = translate props spec_insuf in
  let test_params =
    if native_precond_generated then
      begin
	let domains, unquantifs, quantifs =
	  let add_global (d, u, q) v = Sd_native_precond.add_global v d u q in
	  List.fold_left add_global (domains,unquantifs,quantifs) new_globals
	in
	Sd_native_precond.translate precond_fname domains unquantifs quantifs;
	Printf.sprintf "-pc-test-params %s" precond_fname
      end
    else ""
  in
  print_translation instru_fname insertions spec_insuf;
  let cmd =
    Printf.sprintf
      "frama-c -add-path /usr/local/lib/frama-c/plugins %s -main %s -lib-entry \
 -pc -pc-gmp -pc-validate-asserts %s -pc-com %s -pc-no-xml %s -pc-deter"
      instru_fname
      entry_point
      test_params
      (Sd_options.Socket_Type.get())
      (Sd_options.PathCrawler_Options.get())
  in
  Sd_options.Self.debug ~dkey:Sd_options.dkey_socket "cmd: %s" cmd;
  (* open socket with the generator *)
  begin
    match Sd_options.Socket_Type.get() with
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
	      Sd_socket.process_socket client;
	      Sd_socket.print_exit_code ret;
	      aux (cpt+1)
	  in
	  aux 0
	with _ ->
	  Unix.close socket;
	  Sd_options.Self.abort "unix socket now closed!"
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
	      Sd_socket.process_socket client;
	      Sd_socket.print_exit_code ret;
	      aux (cpt+1)
	  in
	  aux 0
	with _ ->
	  Unix.close socket;
	  Sd_options.Self.abort "internet socket now closed!"
      end;
      Unix.close socket
    | _ (* stdio *) ->
      let chan = Unix.open_process_in cmd in
      Sd_socket.process_channel chan;
      let ret = Unix.close_process_in chan in
      Sd_socket.print_exit_code ret
  end;
  Sd_states.NbCases.mark_as_computed();
  Sd_states.TestFailures.mark_as_computed();
  Sd_states.Unreachable_Stmts.mark_as_computed();
  Sd_options.Self.result "all-paths: %b" (Sd_states.All_Paths.get());
  Sd_options.Self.result "%i test cases" (Sd_states.NbCases.get());
  let distinct = true in
  let strengthened_precond =
    try
      let bhv = Sd_utils.default_behavior kf in
      let typically_preds = Sd_utils.typically_preds bhv in
      List.map (Property.ip_of_requires kf Kglobal bhv) typically_preds
    with _ -> []
  in
  let emit_status prop =
    try
      let _ = Sd_states.TestFailures.find prop in
      let status = Property_status.False_and_reachable in
      Property_status.emit emitter ~hyps:[] prop ~distinct status
    with
    | Not_found ->
      let status = Property_status.True in
      let hyps = strengthened_precond in
      if Sd_states.All_Paths.get() then
	Property_status.emit emitter ~hyps prop ~distinct status
  in
  List.iter emit_status translated_props;
  let dkey = Sd_options.dkey_reach in
  let add_assert_false sid (stmt, kf) =
    Sd_options.Self.feedback ~dkey "stmt %i unreachable" sid;
    Annotations.add_assert ~kf emitter stmt Logic_const.pfalse
  in
  let info_reachability _ (kf,bhv,is_reachable) =
    Sd_options.Self.feedback ~dkey "behavior '%s' of function '%s' %s"
      bhv.b_name
      (Kernel_function.get_name kf)
      (if is_reachable then "reachable" else "not reachable")
  in
  if Sd_states.All_Paths.get() && strengthened_precond = [] then
    begin
      Sd_states.Unreachable_Stmts.iter add_assert_false;
      if Sd_options.Behavior_Reachability.get() then
	Sd_states.Behavior_Reachability.iter info_reachability
    end


let run() =
  if Sd_options.Enabled.get() then
    begin
      setup_props_bijection();
      do_externals();
      compute_props ();
      Sd_states.Id_To_Property.clear();
      Sd_states.Property_To_Id.clear();
      Sd_states.Not_Translated_Predicates.clear();
      Sd_states.Behavior_Reachability.clear();
      Sd_options.mpz_t := None;
      Sd_states.Externals.clear()
    end


let extern_run () =
  Sd_options.Enabled.set true;
  run ()

let extern_run = Dynamic.register ~plugin:"stady" ~journalize:true "run_stady"
  (Datatype.func Datatype.unit Datatype.unit) extern_run


let run =
  let deps = [Ast.self; Sd_options.Enabled.self] in
  let f, _self = State_builder.apply_once "stady" deps run in
  f
    
let () = Db.Main.extend run
