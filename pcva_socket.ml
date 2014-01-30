


(* messages reçus via socket :
   @FC:TC|N|info:Prop_ID|x1=v1|x2=v2 ...
   @FC:FinalStatus|OK
   @FC:NbTC|N
*)


(* coupe une chaîne en deux *)
let cut s n =
  try (String.sub s 0 n), (String.sub s n ((String.length s)-n))
  with _ -> Options.Self.abort "socket:cut \"%s\" %i" s n

let process_test_case s =
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
  let prop = Prop_id.to_prop id_prop in
  let file = Options.Temp_File.get() in
  let func = Kernel_function.get_name (fst (Globals.entry_point ())) in
  let f = "testcases_" ^ (Filename.chop_extension file) in
  let f = Filename.concat f func in
  let f = Filename.concat f "testdrivers" in
  let f = Filename.concat f ("TC_" ^ str_tc ^ ".c") in
  let testcases = try States.TestFailures.find prop with _ -> [] in
  States.TestFailures.add prop ((f, list_entries)::testcases)

let process_nb_test_cases s = States.NbCases.set (int_of_string s)
let process_final_status () = Prop_id.all_paths := true
    


(* le mot-clé au début de la chaîne permet de savoir que faire des données
   en fin de chaîne, on se redirige vers la fonction de traitement
   correspondante *)
let process_string s =
  try
    let s1, s2 = cut s 3 in
    if s1 = "TC|" then process_test_case s2
    else
      let s1, s2 = cut s 5 in
      if s1 = "NbTC|" then process_nb_test_cases s2
      else
	let s1, _s2 = cut s 14 in
	if s1 = "FinalStatus|OK" then process_final_status ()
	else Options.Self.debug ~dkey:Options.dkey_socket "'%s' not processed" s
  with _ -> Options.Self.debug ~dkey:Options.dkey_socket "'%s' not processed" s


(* filtre les chaînes de caractères reçues, on ne traite que celles qui
   sont préfixées par @FC: *)
let rec process_channel c =
  try
    let str = input_line c in
    begin
      if str <> "" then
	let prefix, suffix = cut str 4 in
	if prefix = "@FC:" then process_string suffix
    end;
    process_channel c
  with End_of_file -> ()


(* récupère le cannal d'écoute de la socket *)
let process_socket s =
  let in_chan = Unix.in_channel_of_descr s in
  process_channel in_chan;
  close_in in_chan



let print_exit_code code =
  let str =
    match code with
    | Unix.WEXITED _ -> "OK"
    | Unix.WSIGNALED _ ->  "killed"
    | Unix.WSTOPPED _ -> "stopped"
  in
  Options.Self.feedback ~dkey:Options.dkey_socket "PathCrawler %s!" str
    
