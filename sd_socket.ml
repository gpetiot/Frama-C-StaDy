
let process_test_case s =
  let cut_sep sep x = Extlib.string_split x (String.index x sep) in
  let str_tc, s = cut_sep '|' s in
  let _msg, s = cut_sep ':' s in
  let str_prop, s = try cut_sep '|' s with _ -> s, "" in
  let id_prop = int_of_string str_prop in
  let kind, s = try cut_sep '|' s with _ -> s, "" in
  if kind <> "IN" && kind <> "OUTCONC" && kind <> "OUTSYMB" then
    Sd_options.Self.abort "wrong value for kind: %s" kind;
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
  let func = Kernel_function.get_name (fst (Globals.entry_point ())) in
  let instru_file_name =
    Printf.sprintf "__sd_instru_%s_%s.c"
      (Filename.chop_extension(Filename.basename(List.hd (Kernel.Files.get()))))
      func
  in
  let f = "testcases_" ^ (Filename.chop_extension instru_file_name) in
  let f = Filename.concat f func in
  let f = Filename.concat f "testdrivers" in
  let f = Filename.concat f ("TC_" ^ str_tc ^ ".c") in
  let file_tbl =
    try Sd_states.Counter_examples.find prop
    with Not_found -> Datatype.String.Hashtbl.create 32
  in
  let var_tbl =
    try Datatype.String.Hashtbl.find file_tbl f
    with Not_found -> Datatype.String.Hashtbl.create 32
  in
  let on_pair (var, value) =
    let i, c, s =
      try Datatype.String.Hashtbl.find var_tbl var
      with Not_found -> "", "", ""
    in
    let i, c, s =
      if kind = "IN" then value,c,s
      else if kind = "OUTCONC" then i,value,s
      else i,c,value
    in
    Datatype.String.Hashtbl.replace var_tbl var (i,c,s)
  in
  List.iter on_pair list_entries;
  Datatype.String.Hashtbl.replace file_tbl f var_tbl;
  Sd_states.Counter_examples.replace prop file_tbl


let process_nb_test_cases s = Sd_states.Nb_test_cases.set (int_of_string s)

let process_final_status () = Sd_states.All_Paths.set true
    
let process_reachable_stmt s =
  Sd_states.Unreachable_Stmts.remove (int_of_string s)

let process_reachable_bhv s =
  let id = int_of_string s in
  let kf,bhv,_ = Sd_states.Behavior_Reachability.find id in
  Sd_states.Behavior_Reachability.replace id (kf,bhv,true)


(* le mot-clé au début de la chaîne permet de savoir que faire des données
   en fin de chaîne, on se redirige vers la fonction de traitement
   correspondante *)
let process_string s =
  try
    let s1, s2 = Extlib.string_split s 2 in
    if s1 = "TC" then process_test_case s2
    else
      let s1, s2 = Extlib.string_split s 4 in
      if s1 = "NbTC" then process_nb_test_cases s2
      else
	if s = "FinalStatus|OK" then process_final_status ()
	else
	  let s1, s2 = Extlib.string_split s 13 in
	  if s1 = "REACHABLE_BHV" then process_reachable_bhv s2
	  else
	    let s1, s2 = Extlib.string_split s 14 in
	    if s1 = "REACHABLE_STMT" then process_reachable_stmt s2
	    else assert false
  with _ ->
    Sd_options.Self.debug ~dkey:Sd_options.dkey_socket "'%s' not processed" s


(* filtre les chaînes de caractères reçues, on ne traite que celles qui
   sont préfixées par @FC: *)
let rec process_channel c =
  try
    let str = input_line c in
    begin
      if str <> "" then
	let dkey = Sd_options.dkey_socket in
	Sd_options.Self.debug ~dkey "'%s' received" str;
	let prefix, suffix = Extlib.string_split str 3 in
	if prefix = "@FC" then process_string suffix
	else Sd_options.Self.debug ~dkey "'%s' not processed" str
    end;
    process_channel c
  with End_of_file -> ()


(* récupère le cannal d'écoute de la socket *)
let process_socket s =
  let in_chan = Unix.in_channel_of_descr s in
  process_channel in_chan;
  close_in in_chan


let print_exit_code code =
  let str = match code with
    | Unix.WEXITED _ -> "OK"
    | Unix.WSIGNALED _ ->  "killed"
    | Unix.WSTOPPED _ -> "stopped"
  in
  Sd_options.Self.feedback ~dkey:Sd_options.dkey_socket "PathCrawler %s!" str
    
