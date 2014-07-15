
open Cil_types


let typically_typer ~typing_context ~loc bhv ps =
  match ps with
  | p::[] ->
    bhv.b_extended <-
      ("typically",42,
       [Logic_const.new_predicate 
           (typing_context.Logic_typing.type_predicate 
	      (typing_context.Logic_typing.pre_state) 
	      p)])
    ::bhv.b_extended
  | _ -> typing_context.Logic_typing.error loc
    "expecting a predicate after keyword 'typically'"

let () = Logic_typing.register_behavior_extension "typically" typically_typer


let second_pass filename props =
  Kernel.Unicode.set false;

  let gatherer = new Sd_printer.gather_insertions props in
  Visitor.visitFramacFile (gatherer :> Visitor.frama_c_inplace) (Ast.get());
  let insertions = gatherer#get_insertions() in

  Hashtbl.iter (fun k v ->
    Sd_options.Self.feedback "%a" Sd_printer.pp_label k;
    let print s = Sd_options.Self.feedback "%s" s in
    Queue.iter print v;
    Sd_options.Self.feedback "----------"
  ) insertions;

  (* let printer = new Sd_printer.sd_printer props () in *)
  let printer = new Sd_printer.print_insertions insertions ~print_label:false () in
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
  gatherer#translated_properties()


let emitter =
  Emitter.create "StaDy" [Emitter.Property_status; Emitter.Funspec]
    ~correctness:[] ~tuning:[]


let compute_props props =
  let precond_file_name =
    Printf.sprintf "__sd_%s_%s.pl"
      (Filename.chop_extension(Filename.basename(List.hd (Kernel.Files.get()))))
      (Kernel_function.get_name (fst(Globals.entry_point())))
  in
  let instru_file_name =
    Printf.sprintf "__sd_instru_%s_%s.c"
      (Filename.chop_extension(Filename.basename(List.hd (Kernel.Files.get()))))
      (Kernel_function.get_name (fst(Globals.entry_point())))
  in

  (* Translate some parts of the pre-condition in Prolog *)
  let native_precond_generated =
    try Sd_native_precond.translate precond_file_name; true with _ -> false in
  Sd_options.Self.feedback ~dkey:Sd_options.dkey_native_precond
    "Prolog pre-condition %s generated"
    (if native_precond_generated then "successfully" else "not");
  let kf = fst (Globals.entry_point()) in
  let translated_props =
    second_pass instru_file_name props in
  let test_params =
    if native_precond_generated then
      Printf.sprintf "-pc-test-params %s" precond_file_name
    else
      ""
  in
  let cmd =
    Printf.sprintf
      "frama-c -add-path /usr/local/lib/frama-c/plugins %s -main %s -pc -pc-gmp -pc-validate-asserts %s -pc-com %s -pc-no-xml %s"
      instru_file_name
      (Kernel_function.get_name (fst(Globals.entry_point())))
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
	    if cpt = 3 then ()
	    else
	      let client, _ = Unix.accept socket in
	      Sd_socket.process_socket client;
	      Sd_socket.print_exit_code ret;
	      aux (cpt+1)
	  in
	  aux 0
	with _ ->
	  Unix.close socket;
	  Sd_options.Self.feedback ~dkey:Sd_options.dkey_socket
	    "error: unix socket now closed!"
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
	    if cpt = 3 then ()
	    else
              let client, _ = Unix.accept socket in
	      Sd_socket.process_socket client;
	      Sd_socket.print_exit_code ret;
	      aux (cpt+1)
	  in
	  aux 0
	with _ ->
	  Unix.close socket;
	  Sd_options.Self.feedback ~dkey:Sd_options.dkey_socket
	    "error: internet socket now closed!"
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
  List.iter (fun prop ->
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
  ) translated_props;
  if Sd_states.All_Paths.get() && strengthened_precond = [] then
    begin
      Sd_states.Unreachable_Stmts.iter (fun sid (stmt, kf) ->
	Sd_options.Self.feedback "stmt %i unreachable" sid;
	Annotations.add_assert ~kf emitter stmt Logic_const.pfalse
      );
      if Sd_options.Behavior_Reachability.get() then
	Sd_states.Behavior_Reachability.iter (fun _ (kf,bhv,is_reachable) ->
	  Sd_options.Self.feedback "behavior '%s' of function '%s' %s"
	    bhv.b_name
	    (Kernel_function.get_name kf)
	    (if is_reachable then "reachable" else "not reachable")
	)
    end


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


let properties_of_behavior : string -> Property.t list =
  fun name ->
    Property_status.fold (fun p ret ->
      match Property.get_behavior p with
      | Some b when b.b_name = name -> p :: ret
      | _ -> ret
    ) []


let properties_of_function : string -> Property.t list =
  fun name ->
    Property_status.fold (fun p ret ->
      match Property.get_kf p with
      | Some kf when (Kernel_function.get_name kf) = name -> p :: ret
      | _ -> ret
    ) []


let properties_of_name : string -> Property.t list =
  fun name ->
    Property_status.fold (fun p ret ->
      let str =
	try
	  let buf = Buffer.create 32 in
	  let fmt = Format.formatter_of_buffer buf in
	  Property.short_pretty fmt p;
	  Format.pp_print_flush fmt ();
	  let str = Buffer.contents buf in
	  Buffer.clear buf;
	  str
	with _ -> ""
      in
      if str <> "" && str = name then p :: ret else ret
    ) []


let run() =
  if Sd_options.Enabled.get() then
    begin
      setup_props_bijection();
      let properties = Sd_options.Properties.get () in
      let behaviors = Sd_options.Behaviors.get () in
      let functions = Sd_options.Functions.get () in

      let gather p b = List.rev_append (properties_of_behavior b) p in
      let props = List.fold_left gather [] behaviors in
      let gather p f = List.rev_append (properties_of_function f) p in
      let props = List.fold_left gather props functions in
      let gather p n = List.rev_append (properties_of_name n) p in
      let props = List.fold_left gather props properties in
      let props =
	if props = [] then
	  Property_status.fold (fun p l -> p :: l) []
	else
	  props
      in

      let props = List.filter (fun p ->
	match Property_status.get p with
	| Property_status.Inconsistent _
	| Property_status.Best (Property_status.True,_)
	| Property_status.Best (Property_status.False_if_reachable,_)
	| Property_status.Best (Property_status.False_and_reachable,_) -> false
	| Property_status.Never_tried
	| Property_status.Best (Property_status.Dont_know,_) -> true
      ) props in


      Sd_options.Self.debug
	~dkey:Sd_options.dkey_properties "selected properties:";
      List.iter (fun p ->
	try
	  let id = Sd_utils.to_id p in
	  Sd_options.Self.debug ~dkey:Sd_options.dkey_properties
	    "%a (%i) found" Property.pretty p id
	with _ -> Sd_options.Self.debug ~dkey:Sd_options.dkey_properties
	  "%a not found" Property.pretty p
      ) props;

      compute_props props;


      (* cleaning *)
      Sd_states.Id_To_Property.clear();
      Sd_states.Property_To_Id.clear();
      Sd_states.Not_Translated_Predicates.clear();
      Sd_states.Behavior_Reachability.clear()
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
