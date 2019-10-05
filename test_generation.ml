let process_test_case s =
  let cut_sep sep x = Extlib.string_split x (String.index x sep) in
  let str_tc, s = cut_sep '|' s in
  let msg, s = cut_sep ':' s in
  let str_prop, s = try cut_sep '|' s with _ -> (s, "") in
  let id_prop = int_of_string str_prop in
  let kind, s = try cut_sep '|' s with _ -> (s, "") in
  if kind <> "IN" && kind <> "OUTCONC" && kind <> "OUTSYMB" then
    Options.warning "wrong value for kind: %s" kind
  else
    let add_var_val acc str =
      try
        let x, y = cut_sep '=' str in
        (x, y) :: acc
      with _ -> acc
    in
    let list_entries =
      let rec aux acc str =
        try
          let x, y = cut_sep '|' str in
          aux (add_var_val acc x) y
        with _ -> add_var_val acc str
      in
      if s = "" then [] else aux [] s
    in
    let prop = Utils.to_prop id_prop in
    let ignore_var v =
      try
        String.sub v 0 7 = "nondet_"
        && String.sub v (String.rindex v '_') 4 = "_cpt"
      with _ -> false
    in
    try
      (* '$' only present when a SW is found *)
      let str_stmt_id, msg = cut_sep '$' msg in
      let str_stmt_ids =
        let rec aux acc str =
          try
            let x, y = cut_sep ',' str in
            aux (x :: acc) y
          with _ -> str :: acc
        in
        aux [] str_stmt_id
      in
      let stmt_ids = List.map int_of_string str_stmt_ids in
      let find_stmt sid = fst (Kernel_function.find_from_sid sid) in
      let stmts = List.map find_stmt stmt_ids in
      SWCE.register ignore_var kind prop str_tc msg stmts list_entries
    with _ -> NCCE.register ignore_var kind prop str_tc msg list_entries

let process_nb_test_cases s = States.Nb_test_cases.set (int_of_string s)

let process_final_status () = States.All_Paths.set true

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
      else if s = "FinalStatus|OK" then process_final_status ()
      else assert false
  with _ -> Options.debug ~dkey:Options.dkey_socket "'%s' not processed" s

(* filtre les chaînes de caractères reçues, on ne traite que celles qui
   sont préfixées par @FC: *)
let rec process_channel c =
  try
    let str = input_line c in
    if str <> "" then (
      let dkey = Options.dkey_socket in
      Options.debug ~dkey "'%s' received" str ;
      let prefix, suffix = Extlib.string_split str 3 in
      if prefix = "@FC" then process_string suffix
      else Options.debug ~dkey "'%s' not processed" str ) ;
    process_channel c
  with End_of_file -> ()

(* récupère le cannal d'écoute de la socket *)
let process_socket s =
  let in_chan = Unix.in_channel_of_descr s in
  process_channel in_chan ; close_in in_chan

let print_exit_code code =
  let str =
    match code with
    | Unix.WEXITED _ -> "OK"
    | Unix.WSIGNALED _ -> "killed"
    | Unix.WSTOPPED _ -> "stopped"
  in
  Options.feedback ~dkey:Options.dkey_socket "PathCrawler %s!" str

let run ~entry_point ~precondition_filename ~instrumented_filename =
  let stop_when_assert_violated =
    if Options.Stop_When_Assert_Violated.get () then
      "-pc-stop-when-assert-violated"
    else ""
  in
  let cmd =
    Printf.sprintf
      "%s %s -main %s -lib-entry -variadic-no-translation -pc -pc-gmp \
       -pc-validate-asserts -pc-test-params %s -pc-com %s -pc-no-xml \
       -pc-deter -pc-session-timeout=%i %s -pc-verbose 0 %s"
      Sys.argv.(0)
      instrumented_filename entry_point precondition_filename
      (Options.Socket_Type.get ())
      (Options.Timeout.get ()) stop_when_assert_violated
      (Options.PathCrawler_Options.get ())
  in
  Options.debug ~dkey:Options.dkey_socket "cmd: %s" cmd ;
  match Options.Socket_Type.get () with
  | "unix" ->
      let socket = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
      let name = "Pc2FcSocket" in
      ( try
          Unix.bind socket (Unix.ADDR_UNIX name) ;
          Unix.listen socket 2 ;
          let ret = Unix.system cmd in
          let rec aux cpt =
            if cpt < 3 then (
              let client, _ = Unix.accept socket in
              process_socket client ;
              print_exit_code ret ;
              aux (cpt + 1) )
          in
          aux 0
        with _ ->
          Unix.close socket ;
          Options.abort "unix socket now closed!" ) ;
      Unix.close socket ; Sys.remove name
  | "internet" ->
      let socket = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
      ( try
          Unix.bind socket (Unix.ADDR_INET (Unix.inet_addr_loopback, 2222)) ;
          Unix.listen socket 2 ;
          let ret = Unix.system cmd in
          let rec aux cpt =
            if cpt < 3 then (
              let client, _ = Unix.accept socket in
              process_socket client ;
              print_exit_code ret ;
              aux (cpt + 1) )
          in
          aux 0
        with _ ->
          Unix.close socket ;
          Options.abort "internet socket now closed!" ) ;
      Unix.close socket
  | _ (* stdio *) ->
      let chan = Unix.open_process_in cmd in
      process_channel chan ;
      let ret = Unix.close_process_in chan in
      print_exit_code ret
