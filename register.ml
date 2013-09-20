
open Cil
open Cil_types
open Lexing

 







(* messages reçus via socket :

   @FC:TestInput|N|x=V
   @FC:FinalStatus|OK
   @FC:NumCases=N
   @FC:Verdict|assert_violated=id:L
   @FC:PathPrefix|N|...
   @FC:NumCase=N
*)


module TestFailures = State_builder.Hashtbl
  (Property.Hashtbl)
  (Datatype.Pair
     (Datatype.String) (* C testcase filename *)
     (Datatype.List
	(Datatype.Pair (Datatype.String) (Datatype.String)))) (* entries *)
  (struct
    let name = "PathCrawler.TestFailures"
    let dependencies = [Ast.self]
    let size = 64
   end)
  
module AllPathsOK = State_builder.False_ref
  (struct
    let name = "PathCrawler.AllPathsOK"
    let dependencies = [Ast.self]
   end)

module NbCases = State_builder.Zero_ref
  (struct
    let name = "PathCrawler.NbCases"
    let dependencies = [Ast.self]
   end)
  

(* val tested_func: unit -> kernel_function *)
let tested_func () = (fst (Globals.entry_point ()))


let asserts_violated_cpt = ref 0
let current_assert_line = ref (-1)
let current_c_testcase = ref ""
let current_entries = ref []


(* coupe une chaîne en deux *)
let cut s n =
  try
    (String.sub s 0 n), (String.sub s n ((String.length s)-n))
  with
  | _ -> Options.Self.debug ~level:2 "cut \"%s\" %i" s n; assert false


let update_status_last_assert() =
  if !current_assert_line <> -1 then
    let line = string_of_int !current_assert_line in
    let str = line (*^ "#" ^ !current_assert_pred*) in
    let prop = Prop_id.to_prop (int_of_string str) in
    TestFailures.add prop (!current_c_testcase, !current_entries);
    current_assert_line := -1;
    current_c_testcase := "";
    current_entries := []
      

(* message du type @FC:Verdict|assert_violated=id:L
   met à KO le statut de la propriété associée à l'assertion ligne L du
   fichier F
   le chemin vers le testcase.xml est récupéré : on peut l'ouvrir dans un
   navigateur via l'interface graphique (clic droit sur une assertion violée) *)
let process_assert_violated s =
  let () = update_status_last_assert () in
  (* il y a ':' dans l'id donc on parse en partant de la fin *)
  let pos = String.rindex s ':' in
  let _, line = cut s (pos+1) in
  let line = int_of_string line in
  current_assert_line := line;
  asserts_violated_cpt := !asserts_violated_cpt + 1


(* message du type @FC:NumCase=i
*)
let process_numcase n =
  let filename = Options.Temp_File.get() in
  let tested_func = Kernel_function.get_name (tested_func()) in
  let testcase_fname = "testcases_" ^ (Filename.chop_extension filename) in
  let testcase_fname = Filename.concat testcase_fname tested_func in
  let testcase_fname_c = Filename.concat testcase_fname "testdrivers" in
  let testcase_fname_c = Filename.concat testcase_fname_c ("TC_" ^ n ^ ".c") in
  current_c_testcase := testcase_fname_c


(* message du type @FC:Verdict|failure=oracle : line L
   met à KO le statut de la postcondition associée à l'échec de l'oracle
   ligne L de la fonction sous test
   le chemin vers le testcase.xml est récupéré : on peut l'ouvrir dans un
   navigateur via l'interface graphique (clic droit sur une postcondition
   violée) *)
let process_oracle s =
  let () = update_status_last_assert () in
  current_assert_line := (int_of_string s);
  asserts_violated_cpt := !asserts_violated_cpt + 1
    

(* message du type @FC:FinalStatus|OK
   positionne à OK le statut associé à chacune des assertions que nous avons
   rajoutées (ACSL assert ==> pc_assert) et qui n'ont pas été violées,
   uniquement si la génération de tests s'est terminée sans problème avec la
   stratégie all-paths *)
let process_asserts() =
  let () = update_status_last_assert () in
  AllPathsOK.set true
    

(* message du type @FC:TestInput|N|x=V
   récupère la valeur V d'une variable d'entrée x pour le cas de test N
   violant une assertion *)
let process_testinput s =
  let pos = String.index s '|' in
  let _, s = cut s (pos+1) in
  let pos = String.index s '=' in
  let name = String.sub s 0 pos in
  let _, value = cut s (pos+1) in
  current_entries := (name, value) :: !current_entries


(* message du type @FC:PathPrefix|N|...
   inutilisé *)
let process_pathprefix _s = ()


(* message du type @FC:NumCases=N *)
let process_numcases s =
  NbCases.set (int_of_string s);
  NbCases.mark_as_computed()


(* le mot-clé au début de la chaîne permet de savoir que faire des données
   en fin de chaîne, on se redirige vers la fonction de traitement
   correspondante *)
let process_string s =
  try
    Options.Self.debug ~level:2 "\"%s\"" s;
    let s1, s2 = cut s 8 in
    if s1 = "NumCase=" then process_numcase s2
    else
      let s1, s2 = cut s 9 in
      if s1 = "NumCases=" then process_numcases s2
      else
	let s1, s2 = cut s 10 in
	if s1 = "TestInput|" then process_testinput s2
	else
	  let s1, s2 = cut s 11 in
	  if s1 = "PathPrefix|" then process_pathprefix s2
	  else
	    let s1, _ = cut s 14 in
	    if s1 = "FinalStatus|OK" then process_asserts()
	    else
	      let s1, _ = cut s 15 in
	      if s1 = "Verdict|success" then ()
	      else
		let s1, s2 = cut s 24 in
		if s1 = "Verdict|assert_violated=" then
		  process_assert_violated s2
		else
		  let s1, s2 = cut s 30 in
		  if s1 = "Verdict|failure=oracle : line " then
		    process_oracle s2
  with
  | exc ->
    Options.Self.debug ~level:2 "%s" (Printexc.to_string exc);
    Options.Self.debug ~level:2 "'%s' not processed" s


(* filtre les chaînes de caractères reçues, on ne traite que celles qui
   sont préfixées par @FC: *)
let rec process_channel c =
  try
    let str = input_line c in
    let () =
      if str <> "" then
	let prefix, suffix = cut str 4 in
	let () = if prefix = "@FC:" then process_string suffix in
	()
    in
    process_channel c
  with
    | End_of_file -> update_status_last_assert()


(* récupère le cannal d'écoute du socket *)
let process_socket s =
  let in_chan = Unix.in_channel_of_descr s in
  let () = process_channel in_chan in
  let () = close_in in_chan in
  let () = AllPathsOK.mark_as_computed() in
  let () = TestFailures.mark_as_computed() in
  asserts_violated_cpt := 0



let print_exit_code = function
  | Unix.WEXITED _ -> Options.Self.feedback "PathCrawler OK"
  | Unix.WSIGNALED _ -> Options.Self.feedback "PathCrawler killed!"
  | Unix.WSTOPPED _ -> Options.Self.feedback "PathCrawler stopped!"



(***************************************************************)






(* extern functions *)
module Annot_Precond = struct
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
end




(* outputs the AST of a project in a file *)
let print_in_file prj filename =
  Project.on prj (fun () ->
    (* first pass: prepare the quantifiers predicates, ignore the output *)
    let fmt = Format.make_formatter (fun _ _ _ -> ()) ignore in
    Pcva_printer.First_pass.pp_file fmt (Ast.get());

    (* second pass: print the instrumented quantif, output in a file *)
    let out = open_out filename in
    let fmt = Format.formatter_of_out_channel out in
    Pcva_printer.Second_pass.pp_file fmt (Ast.get());
    flush out;
    close_out out
  ) ()



let pcva_emitter =
  Emitter.create "pcva" [Emitter.Property_status; Emitter.Funspec]
    ~correctness:[] ~tuning:[]



let run() =
  if Options.Enabled.get() then
    begin
      (* Settings *)
      Kernel.Unicode.set false;

      (* Bijection :
	 unique_identifier <--> property
      *)
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
      );


      (* Translate some parts of the pre-condition in Prolog *)
      Annot_Precond.generate_test_parameters();
      Options.Self.feedback "Prolog precondition successfully generated";
      let parameters_file = Annot_Precond.out_file () in
      Options.Self.feedback "The result is in file %s" parameters_file;

      (* Save the result in a file *)
      print_in_file (Project.current()) (Options.Temp_File.get());
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
	      process_socket client;
	      print_exit_code ret
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
	      (* TODO: envoyer le numéro de port à Eclipse Prolog,
		 éviter de coder ce numéro en dur, idem dans le code Prolog *)
	      Unix.bind socket(Unix.ADDR_INET(Unix.inet_addr_loopback,2222));
	      Unix.listen socket 1;
	      let ret = Unix.system cmd in
	      let client, _ = Unix.accept socket in
	      process_socket client;
	      print_exit_code ret
	    with _ ->
	      Unix.close socket;
	      Options.Self.feedback "error: internet socket now closed!"
	  end;
	  Unix.close socket
	| _ (* stdio *) ->
	  let chan = Unix.open_process_in cmd in
	  process_channel chan;
	  let ret = Unix.close_process_in chan in
	  print_exit_code ret
      end;

      Options.Self.feedback "all-paths: %b" (AllPathsOK.get());
      Options.Self.feedback "%i test cases" (NbCases.get());

      let t_l = List.fold_left (fun x y ->
	Printf.sprintf "%s %i" x (Prop_id.to_id y)
      ) "" translated_properties in
      Options.Self.feedback "translated properties: %s" t_l;

      
      (* For some reason, the test case entries are duplicated, so we fix it *)
      TestFailures.iter (fun x (y,entries) ->
	TestFailures.replace x (y, Pcva_printer.no_repeat entries)
      );


      let e_acsl_present = Dynamic.is_plugin_present "E_ACSL" in
      if not e_acsl_present then
	Options.Self.feedback
	  "E-ACSL not found, counter-examples will not be confirmed!";
      

      List.iter (fun prop ->
	try
	  let c_test_case, entries = TestFailures.find prop in
	  let status =
	    if c_test_case <> "" then
	      begin
	      (* change the include of the C test-case -- UGLY *)
		let tmp = "__pcva__temp.c" in
		let cmd =
		  Printf.sprintf "sed -e s/%s/%s/ %s > %s"
		    (Options.Temp_File.get())
		    (List.hd(Kernel.Files.get()))
		    c_test_case
		    tmp
		in
		let _ = Sys.command cmd in
		let cmd = Printf.sprintf "cp %s %s" tmp c_test_case in
		let _ = Sys.command cmd in

		(* confirm the bug by execution using E-ACSL *)
		if e_acsl_present then
		  let out = "pcva_exec" in
		  let cmd =
		    Printf.sprintf
		      "frama-c %s -rte -rte-verbose 0 -then -val -value-verbose 0 -then -e-acsl -then-on e-acsl -print -ocode %s.c"
		      c_test_case
		      out
		  in
		  let _ = Sys.command cmd in
		  let cmd =
		    Printf.sprintf
		      "gcc -w %s.c %s %s %s -o %s.out -lgmp && ./%s.out"
		      out
		      "/usr/local/share/frama-c/e-acsl/e_acsl.c"
		      "/usr/local/share/frama-c/e-acsl/memory_model/e_acsl_mmodel.c"
		      "/usr/local/share/frama-c/e-acsl/memory_model/e_acsl_bittree.c"
		      out
		      out
		  in
		  let ret = Sys.command cmd in
		  Options.Self.feedback "Bug of property %i %s by E-ACSL" 
		    (Prop_id.to_id prop)
		    (if ret = 0 then "NOT confirmed" else "confirmed");
		  if ret = 0 then
		    Property_status.False_if_reachable
		  else
		    Property_status.False_and_reachable
		else (* e-acsl not found *)
		  Property_status.False_if_reachable
	      end
	    else (* test case not generated *)
	      Property_status.False_if_reachable
	  in


	  List.iter (fun (x,y) ->
	    Options.Self.debug~level:1 "%s = %s" x y) entries;
	  Options.Self.debug ~level:1 "------------------";
	  Options.Self.debug ~level:1 "prop %i in counter-examples table"
	    (Prop_id.to_id prop);
	  let hyps = [] in
	  let distinct = true in
	  Property_status.emit pcva_emitter ~hyps prop ~distinct status
	with
	| Not_found ->
	  (* NK does not agree on this condition *)
	  (*if (AllPathsOK.get()) then*)
	    let hyps = [] in
	    let distinct = true in
	    let status = Property_status.True in
	    Property_status.emit pcva_emitter ~hyps prop ~distinct status
      ) translated_properties;


      (* cleaning *)
      Datatype.Int.Hashtbl.clear Prop_id.id_to_prop_tbl;
      Property.Hashtbl.clear Prop_id.prop_to_id_tbl;
      Prop_id.translated_properties := [];
      Pcva_printer.quantif_pred_cpt := 0;
      Queue.clear Pcva_printer.quantif_pred_queue;
      Pcva_printer.postcond := None;
      Pcva_printer.at_term_cpt := 0;
      Datatype.String.Hashtbl.clear Pcva_printer.at_term_affect_in_function

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
  
