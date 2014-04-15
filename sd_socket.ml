
(* cut a string into 2 pieces *)
let cut : string -> int -> string * string =
  fun s n ->
    try (String.sub s 0 n), (String.sub s n ((String.length s)-n))
    with _ -> Sd_options.Self.abort "socket:cut \"%s\" %i" s n

let process_test_case : string -> unit =
  fun s ->
    let cut_sep sep x =
      let pos = String.index x sep in
      let a,_ = cut x pos in
      let _,b = cut x (pos+1) in
      a,b
    in
    let str_tc, s = cut_sep '|' s in
    let _msg, s = cut_sep ':' s in
    let str_prop, s = try cut_sep '|' s with _ -> s, "" in
    let id_prop = int_of_string str_prop in
    let kind, s = try cut_sep '|' s with _ -> s, "" in
    if kind <> "IN" && kind <> "OUTCONC" && kind <> "OUTSYMB" then
      (Sd_options.Self.debug
	 ~dkey:Sd_options.dkey_socket "wrong value for kind: %s" kind;
       assert false);
    let add_var_val acc str =
      try let x, y = cut_sep '=' str in (x,y)::acc
      with _ -> acc
    in
    let list_entries =
      let rec aux acc str =
	try let x,y = cut_sep '|' str in aux (add_var_val acc x) y
	with _ -> add_var_val acc str
      in
      if s = "" then [] else aux [] s
    in
    let prop = Sd_utils.to_prop id_prop in
    let file = Sd_options.Temp_File.get() in
    let func = Kernel_function.get_name (fst (Globals.entry_point ())) in
    let f = "testcases_" ^ (Filename.chop_extension file) in
    let f = Filename.concat f func in
    let f = Filename.concat f "testdrivers" in
    let f = Filename.concat f ("TC_" ^ str_tc ^ ".c") in
    try
      let tbl = Sd_states.TestFailures.find prop in
      try
	let input,conc,symb = Datatype.String.Hashtbl.find tbl f in
	let input, conc, symb =
	  if kind = "IN" then list_entries, conc, symb
	  else if kind = "OUTCONC" then input, list_entries, symb
	  else input, conc, list_entries
	in
	Datatype.String.Hashtbl.replace tbl f (input,conc,symb);
	Sd_states.TestFailures.replace prop tbl
      with
      | _ ->
	let input, conc, symb =
	  if kind = "IN" then list_entries, [], []
	  else if kind = "OUTCONC" then [], list_entries, []
	  else [], [], list_entries
	in
	Datatype.String.Hashtbl.add tbl f (input,conc,symb);
	Sd_states.TestFailures.replace prop tbl
    with
    | _ ->
      (* no counter-example for considered property *)
      let new_tbl = Datatype.String.Hashtbl.create 32 in
      let input, conc, symb =
	if kind = "IN" then list_entries, [], []
	else if kind = "OUTCONC" then [], list_entries, []
	else [], [], list_entries
      in
      Datatype.String.Hashtbl.add new_tbl f (input,conc,symb);
      Sd_states.TestFailures.add prop new_tbl

let process_nb_test_cases : string -> unit =
  fun s -> Sd_states.NbCases.set (int_of_string s)

let process_final_status : unit -> unit =
  fun () -> Sd_states.All_Paths.set true
    


(* le mot-clé au début de la chaîne permet de savoir que faire des données
   en fin de chaîne, on se redirige vers la fonction de traitement
   correspondante *)
let process_string : string -> unit =
  fun s ->
    try
      let s1, s2 = cut s 3 in
      if s1 = "TC|" then process_test_case s2
      else
	let s1, s2 = cut s 5 in
	if s1 = "NbTC|" then process_nb_test_cases s2
	else
	  let s1, _s2 = cut s 14 in
	  if s1 = "FinalStatus|OK" then process_final_status ()
	  else assert false
    with _ ->
      Sd_options.Self.debug ~dkey:Sd_options.dkey_socket "'%s' not processed" s


(* filtre les chaînes de caractères reçues, on ne traite que celles qui
   sont préfixées par @FC: *)
let rec process_channel : in_channel -> unit =
  fun c ->
    try
      let str = input_line c in
      begin
	if str <> "" then
	  let dkey = Sd_options.dkey_socket in
	  Sd_options.Self.debug ~dkey "'%s' received" str;
	  let prefix, suffix = cut str 4 in
	  if prefix = "@FC:" then process_string suffix
	  else Sd_options.Self.debug ~dkey "'%s' not processed" str
      end;
      process_channel c
    with End_of_file -> ()


(* récupère le cannal d'écoute de la socket *)
let process_socket : Unix.file_descr -> unit =
  fun s ->
    let in_chan = Unix.in_channel_of_descr s in
    process_channel in_chan;
    close_in in_chan



let print_exit_code : Unix.process_status -> unit =
  fun code ->
    let str =
      match code with
      | Unix.WEXITED _ -> "OK"
      | Unix.WSIGNALED _ ->  "killed"
      | Unix.WSTOPPED _ -> "stopped"
    in
    Sd_options.Self.feedback ~dkey:Sd_options.dkey_socket "PathCrawler %s!" str
    
