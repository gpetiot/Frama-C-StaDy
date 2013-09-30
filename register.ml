
open Cil
open Cil_types
open Lexing






(* extern functions *)

let generate_test_parameters =
  Dynamic.get
    ~plugin:"Annot_Precond"
    "generate_test_parameters"
    (Datatype.func Datatype.unit Datatype.unit)
    
let out_file =
  Dynamic.get
    ~plugin:"Annot_Precond"
    "out_file"
    (Datatype.func Datatype.unit Datatype.string)
    



(* outputs the AST of a project in a file *)
let print_in_file filename props =
  Kernel.Unicode.set false;
  (* first pass: prepare the quantifiers predicates, ignore the output *)
  let fmt = Format.make_formatter (fun _ _ _ -> ()) ignore in
  let module First_pass = Printer_builder.Make
	(struct class printer =
		  Pcva_printer.pcva_printer props ~first_pass:true end)
  in
  let module Second_pass = Printer_builder.Make
	(struct class printer =
		  Pcva_printer.pcva_printer props ~first_pass:false end)
  in
  First_pass.pp_file fmt (Ast.get());
  (* second pass: print the instrumented quantif, output in a file *)
  let out = open_out filename in
  let fmt = Format.formatter_of_out_channel out in
  Second_pass.pp_file fmt (Ast.get());
  flush out;
  close_out out;
  (* cleaning *)
  Pcva_printer.quantif_pred_cpt := 0;
  Queue.clear Pcva_printer.quantif_pred_queue;
  Pcva_printer.postcond := None;
  Pcva_printer.at_term_cpt := 0;
  Datatype.String.Hashtbl.clear Pcva_printer.at_term_affect_in_function



let pcva_emitter =
  Emitter.create "pcva" [Emitter.Property_status; Emitter.Funspec]
    ~correctness:[] ~tuning:[]


let setup_props_bijection () =
  Datatype.Int.Hashtbl.clear Prop_id.id_to_prop_tbl;
  Property.Hashtbl.clear Prop_id.prop_to_id_tbl;
  (* Bijection: unique_identifier <--> property *)
  let property_id = ref 0 in
  Property_status.iter (fun property ->
    let pos1,_ = Property.location property in
    let fc_builtin = "__fc_builtin_for_normalization.i" in
    if (Filename.basename pos1.pos_fname) <> fc_builtin then
      begin
	Datatype.Int.Hashtbl.add
	  Prop_id.id_to_prop_tbl !property_id property;
	Property.Hashtbl.add Prop_id.prop_to_id_tbl property !property_id;
	property_id := !property_id + 1
      end
  )












let compute_props props =
  (* Translate some parts of the pre-condition in Prolog *)
  generate_test_parameters();
  Options.Self.feedback "Prolog precondition successfully generated";
  let parameters_file = out_file () in
  Options.Self.feedback "The result is in file %s" parameters_file;
  print_in_file (Options.Temp_File.get()) props;
  let translated_properties =
    Pcva_printer.no_repeat !Prop_id.translated_properties in
  let test_params =
    if Sys.file_exists parameters_file then
      Printf.sprintf "-pc-test-params %s" parameters_file
    else
      ""
  in
  let cmd =
    Printf.sprintf
      "frama-c %s -main %s -pc -pc-validate-asserts %s -pc-com %s -pc-no-xml %s"
      (Options.Temp_File.get())
      (Kernel_function.get_name (fst(Globals.entry_point())))
      test_params
      (Options.Socket_Type.get())
      (Options.PathCrawler_Options.get())
  in
  Options.Self.feedback "cmd: %s" cmd;
  (* open socket with the generator *)
  begin
    match Options.Socket_Type.get() with
    | s when s = "unix" ->
      let socket = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
      let name = "Pc2FcSocket" in
      begin
	try
	  Unix.bind socket (Unix.ADDR_UNIX name);
	  Unix.listen socket 1;
	  let ret = Unix.system cmd in
	  let client, _ = Unix.accept socket in
	  Pcva_socket.process_socket client;
	  Pcva_socket.print_exit_code ret
	with _ ->
	  Unix.close socket;
	  Options.Self.feedback "error: unix socket now closed!"
      end;
      Unix.close socket;
      Sys.remove name
    | s when s = "internet" ->
      let socket = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
      begin
	try
	  Unix.bind socket(Unix.ADDR_INET(Unix.inet_addr_loopback,2222));
	  Unix.listen socket 1;
	  let ret = Unix.system cmd in
	  let client, _ = Unix.accept socket in
	  Pcva_socket.process_socket client;
	  Pcva_socket.print_exit_code ret
	with _ ->
	  Unix.close socket;
	  Options.Self.feedback "error: internet socket now closed!"
      end;
      Unix.close socket
    | _ (* stdio *) ->
      let chan = Unix.open_process_in cmd in
      Pcva_socket.process_channel chan;
      let ret = Unix.close_process_in chan in
      Pcva_socket.print_exit_code ret
  end;
  States.NbCases.mark_as_computed();
  States.TestFailures.mark_as_computed();
  Options.Self.feedback "all-paths: %b" !Prop_id.can_validate_others;
  Options.Self.feedback "%i test cases" (States.NbCases.get());
  let hyps = [] in
  let distinct = true in
  List.iter (fun prop ->
    try
      let _ = States.TestFailures.find prop in
      let status = Property_status.False_and_reachable in
      Property_status.emit pcva_emitter ~hyps prop ~distinct status
    with
    | Not_found ->
      let status = Property_status.True in
      if !Prop_id.can_validate_others then
	Property_status.emit pcva_emitter ~hyps prop ~distinct status
  ) translated_properties;
  Prop_id.translated_properties := [];
  Prop_id.can_validate_others := false
  








let run() =
  if Options.Enabled.get() then
    begin
      setup_props_bijection();
      let all_props = Property_status.fold (fun p l -> p :: l) []  in
      compute_props all_props;
      (* cleaning *)
      Datatype.Int.Hashtbl.clear Prop_id.id_to_prop_tbl;
      Property.Hashtbl.clear Prop_id.prop_to_id_tbl
    end



let extern_run () =
  Options.Enabled.set true;
  run ()

let extern_run = Dynamic.register ~plugin:"PCVA" ~journalize:true "run_pcva"
  (Datatype.func Datatype.unit Datatype.unit) extern_run


  
  
let run =
  let deps = [Ast.self; Options.Enabled.self] in
  let f, _self = State_builder.apply_once "pcva" deps run in
  f
    
let () = Db.Main.extend run
  
