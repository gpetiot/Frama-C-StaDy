open Cil_types

let typically_typer ~typing_context ~loc = function
  | [p] ->
      let type_pred = typing_context.Logic_typing.type_predicate in
      let pre_state = typing_context.Logic_typing.pre_state in
      Ext_preds [type_pred typing_context pre_state p]
  | _ ->
      typing_context.Logic_typing.error loc
        "predicate expected after 'typically'"

let () =
  Logic_typing.register_behavior_extension "typically" false typically_typer

let emitter =
  Emitter.create "StaDy"
    [Emitter.Property_status; Emitter.Funspec]
    ~correctness:[] ~tuning:[]

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
    | Some kf when Kernel_function.get_name kf = name -> p :: ret
    | _ -> ret
  in
  Property_status.fold gather []

let properties_of_name name =
  let gather p ret =
    try
      let buf = Buffer.create 32 in
      let fmt = Format.formatter_of_buffer buf in
      Property.short_pretty fmt p ;
      Format.pp_print_flush fmt () ;
      let str = Buffer.contents buf in
      Buffer.clear buf ;
      if str = name then p :: ret else ret
    with _ -> ret
  in
  Property_status.fold gather []

let selected_props () =
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

let compute_props ?(props = selected_props ()) ?swd () =
  let swd =
    match swd with
    | Some x -> x
    | None ->
        let labels = Options.SWD.get () in
        let on_label acc l =
          let on_kf kf = function
            | Some x -> Some x
            | None -> (
              try Some !(Kernel_function.find_label kf l) with Not_found ->
                None )
          in
          try
            let stmt = Extlib.the (Globals.Functions.fold on_kf None) in
            match stmt.skind with
            | Instr (Call _) | Instr (Local_init (_, ConsInit _, _)) | Loop _
              ->
                stmt.sid :: acc
            | _ ->
                Options.failure ~current:true ~once:true
                  "label %s does not refer to a function call nor a loop" l ;
                acc
          with _ ->
            Options.failure ~current:true ~once:true "label %s not found" l ;
            acc
        in
        List.fold_left on_label [] labels
  in
  let files = Kernel.Files.get () in
  let fname = Filename.chop_extension (Filename.basename (List.hd files)) in
  let kf = fst (Globals.entry_point ()) in
  let entry_point = Kernel_function.get_name kf in
  let precond_fname = Printf.sprintf "__sd_%s_%s.pl" fname entry_point in
  let instru_fname = Printf.sprintf "__sd_instru_%s_%s.c" fname entry_point in
  let translated_props =
    Translate.translate props swd precond_fname instru_fname
  in
  Test_generation.run entry_point precond_fname instru_fname ;
  States.Nb_test_cases.mark_as_computed () ;
  States.NC_counter_examples.mark_as_computed () ;
  States.SW_counter_examples.mark_as_computed () ;
  Options.result "all-paths: %b" (States.All_Paths.get ()) ;
  Options.result "%i test cases" (States.Nb_test_cases.get ()) ;
  let strengthened_precond =
    try
      let bhv = Utils.default_behavior kf in
      let typically_preds = Utils.typically_preds bhv in
      List.map (Property.ip_of_requires kf Kglobal bhv) typically_preds
    with _ -> []
  in
  let no_CE = States.NC_counter_examples.length () = 0 in
  let on_prop prop =
    ( match NCCE.one_for prop with
    | Some ncce ->
        Options.result "%a" NCCE.pretty ncce ;
        let status = Property_status.False_and_reachable in
        Property_status.emit emitter ~hyps:[] prop ~distinct:true status
    | None ->
        let status = Property_status.True in
        let hyps = strengthened_precond in
        if States.All_Paths.get () && no_CE && List.mem prop translated_props
        then Property_status.emit emitter ~hyps prop ~distinct:true status ) ;
    Extlib.may (Options.result "%a" SWCE.pretty) (SWCE.one_for prop)
  in
  Property_status.iter on_prop

let run () =
  if Options.Version.get () then Format.printf "%s@." Local_config.version
  else if Options.Enabled.get () then (
    Utils.initialize () ; compute_props () ; Utils.finalize () )

let extern_run () = Options.Enabled.set true ; run ()

let extern_run =
  Dynamic.register ~plugin:"stady" ~journalize:true "run_stady"
    (Datatype.func Datatype.unit Datatype.unit)
    extern_run

let run =
  let deps =
    [ Ast.self
    ; Options.Enabled.self
    ; Options.PathCrawler_Options.self
    ; Options.Socket_Type.self
    ; Options.Timeout.self
    ; Options.Stop_When_Assert_Violated.self
    ; Options.Functions.self
    ; Options.Behaviors.self
    ; Options.Properties.self
    ; Options.SWD.self
    ; Options.Simulate_Functions.self
    ; Options.Precondition.self
    ; Options.Version.self ]
  in
  let f, _self = State_builder.apply_once "stady" deps run in
  f

let () = Db.Main.extend run
