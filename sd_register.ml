
open Cil_types


let typically_typer ~typing_context ~loc bhv ps =
  match ps with
  | p::[] ->
    bhv.b_extended <-
      ("typically",42,
       [Logic_const.new_predicate 
           (typing_context.Logic_typing.type_predicate 
	      (typing_context.Logic_typing.post_state [Normal]) 
	      p)])
    ::bhv.b_extended
  | _ -> typing_context.Logic_typing.error loc
    "expecting a predicate after keyword 'typically'"

let () = Logic_typing.register_behavior_extension "typically" typically_typer


let print_strtbl_vartbl_terms hashtbl dkey =
  Sd_options.Self.debug ~dkey "========================";
  Datatype.String.Hashtbl.iter_sorted (fun f tbl ->
    Sd_options.Self.debug ~dkey "function '%s'" f;
    Cil_datatype.Varinfo.Hashtbl.iter_sorted (fun v ts ->
      Sd_options.Self.debug ~dkey "var '%s'" v.vname;
      List.iter (fun t -> Sd_options.Self.debug ~dkey "%a "Printer.pp_term t) ts
    ) tbl;
    Sd_options.Self.debug ~dkey "----------------"
  ) hashtbl;
  Sd_options.Self.debug ~dkey "========================"


(* Extracts the varinfo of the variable and its inferred size as a term
   from a term t as \valid(t). *)
let rec extract_from_valid : term -> varinfo * term =
  let dkey = Sd_options.dkey_lengths in
  fun t -> match t.term_node with
  | TBinOp((PlusPI|IndexPI),
	   ({term_node=TLval(TVar v, _)} as _t1),
	   ({term_node=Trange(_,Some bound)} as _t2)) ->
    let varinfo = Extlib.the v.lv_origin in
    let tnode = TBinOp (PlusA, bound, Cil.lone ~loc:t.term_loc()) in
    let einfo = {exp_type=bound.term_type; exp_name=[]} in
    let term = Cil.term_of_exp_info t.term_loc tnode einfo in
    varinfo, term

  | TBinOp((PlusPI|IndexPI),
	   ({term_node=TLval(TVar v, _)} as _t1),
	   (t2 (* anything but a Trange *))) ->
    let varinfo = Extlib.the v.lv_origin in
    let tnode = TBinOp (PlusA, t2, Cil.lone ~loc:t.term_loc()) in
    let einfo = {exp_type=t2.term_type; exp_name=[]} in
    let term = Cil.term_of_exp_info t.term_loc tnode einfo in
    varinfo, term

  | TBinOp((PlusPI|IndexPI),
	   ({term_node=TLval tlval}),
	   ({term_node=Trange(_,Some bound)})) ->
    let tnode = TBinOp (PlusA, bound, Cil.lone ~loc:t.term_loc()) in
    let einfo = {exp_type=bound.term_type; exp_name=[]} in
    let term = Cil.term_of_exp_info t.term_loc tnode einfo in
    let varinfo, _ = extract_from_valid {t with term_node=TLval tlval} in
    varinfo, term
    
    

  | TLval (TVar v, TNoOffset) ->
    let varinfo = Extlib.the v.lv_origin in
    let term = Cil.lone ~loc:t.term_loc () in
    varinfo, term
  | TLval (TVar _, TField _) -> assert false
  | TLval (TVar _, TModel _) -> assert false
  | TLval (TVar _, TIndex _) -> assert false
  

  | TLval (TMem m, TNoOffset) ->
    let varinfo, _ = extract_from_valid m in
    let term = Cil.lone ~loc:t.term_loc () in
    varinfo, term
  | TLval (TMem _, TField _) -> assert false
  | TLval (TMem _, TModel _) -> assert false
  | TLval (TMem _, TIndex _) -> assert false


  | TStartOf _ -> Sd_options.Self.debug ~dkey
    "TStartOf \\valid(%a) ignored" Printer.pp_term t;
    assert false
  | TAddrOf _ -> Sd_options.Self.debug ~dkey
    "TAddrOf \\valid(%a) ignored" Printer.pp_term t;
    assert false
  | TCoerce _ -> Sd_options.Self.debug ~dkey
    "TCoerce \\valid(%a) ignored" Printer.pp_term t;
    assert false
  | TCoerceE _ -> Sd_options.Self.debug ~dkey
    "TCoerceE \\valid(%a) ignored" Printer.pp_term t;
    assert false
  | TLogic_coerce _ -> Sd_options.Self.debug ~dkey
    "TLogic_coerce \\valid(%a) ignored" Printer.pp_term t;
    assert false
  | TBinOp _ -> Sd_options.Self.debug ~dkey
    "TBinOp \\valid(%a) ignored" Printer.pp_term t;
    assert false
  | _ -> Sd_options.Self.debug ~dkey "\\valid(%a) ignored" Printer.pp_term t;
    assert false



(* Computes and returns a hashtable such that :
   function_name1 =>
   -  var1 => inferred size for var1
   -  var2 => inferred size for var2
   function_name2 =>
   -  ...
*)
let lengths_from_requires :
    unit
    -> term list Cil_datatype.Varinfo.Hashtbl.t Datatype.String.Hashtbl.t =
  fun () ->
    let lengths = Datatype.String.Hashtbl.create 32 in
    Globals.Functions.iter (fun kf ->
      let vi = Kernel_function.get_vi kf in
      if not (Cil.is_unused_builtin vi) then
	begin
	  let kf_name = Kernel_function.get_name kf in
	  let kf_tbl = Cil_datatype.Varinfo.Hashtbl.create 32 in
	  let o = object
	    inherit Visitor.frama_c_inplace
	    method! vpredicate p =
	      match p with
	      | Pvalid(_, t) | Pvalid_read(_, t) ->
		begin
		  try
		    let v, term = extract_from_valid t in
		    let terms =
		      try Cil_datatype.Varinfo.Hashtbl.find kf_tbl v
		      with Not_found -> []
		    in
		    let terms = Sd_utils.append_end terms term in
		    Cil_datatype.Varinfo.Hashtbl.replace kf_tbl v terms;
		    Cil.DoChildren
		  with
		  | _ -> Cil.DoChildren
		end
	      | _ -> Cil.DoChildren
	  end
	  in
	  Annotations.iter_behaviors (fun _ bhv ->
	    List.iter (fun p ->
	      let p' = (new Sd_subst.subst)#subst_pred p.ip_content [][][][] in
	      ignore (Visitor.visitFramacPredicate o p')
	    ) bhv.b_requires
	  ) kf;
	  (* TODO: handle arrays with constant size *)
	  (*Globals.Vars.iter (fun vi _ -> () );*)
	  Datatype.String.Hashtbl.add lengths kf_name kf_tbl
	end
    );
    Sd_options.Self.debug ~dkey:Sd_options.dkey_lengths "LENGTHS:";
    print_strtbl_vartbl_terms lengths Sd_options.dkey_lengths;
    lengths





(* Computes and returns a hashtable such that :
   function_name1 =>
   -  formal var1 => size of var1 saved
   -  formal var2 => size of var2 saved
   function_name2 =>
   -  ...
*)
let at_from_formals :
    term list Cil_datatype.Varinfo.Hashtbl.t Datatype.String.Hashtbl.t
    -> term list Cil_datatype.Varinfo.Hashtbl.t Datatype.String.Hashtbl.t =
  fun lengths ->
    let terms_at_Pre = Datatype.String.Hashtbl.create 32 in
    Globals.Functions.iter (fun kf ->
      let vi = Kernel_function.get_vi kf in
      if not (Cil.is_unused_builtin vi) then
	let kf_name = Kernel_function.get_name kf in
	let kf_tbl = Cil_datatype.Varinfo.Hashtbl.create 32 in
	let lengths_tbl = Datatype.String.Hashtbl.find lengths kf_name in
	let formals = Kernel_function.get_formals kf in
	let add v = 
	  let terms =
	    try Cil_datatype.Varinfo.Hashtbl.find lengths_tbl v
	    with Not_found -> []
	  in
	  Cil_datatype.Varinfo.Hashtbl.add kf_tbl v terms
	in
	List.iter add formals;
	Globals.Vars.iter (fun v _ -> add v);
	Datatype.String.Hashtbl.add terms_at_Pre kf_name kf_tbl
    );
    Sd_options.Self.debug ~dkey:Sd_options.dkey_at "AT:";
    print_strtbl_vartbl_terms terms_at_Pre Sd_options.dkey_at;
    terms_at_Pre





let second_pass filename props terms_at_Pre =
  Kernel.Unicode.set false;
  let out = open_out filename in
  let fmt = Format.formatter_of_out_channel out in
  let printer = new Sd_printer.sd_printer props terms_at_Pre () in
  printer#file fmt (Ast.get());
  flush out;
  close_out out;
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  printer#file fmt (Ast.get());
  let dkey = Sd_options.dkey_generated_c in
  Format.pp_print_flush fmt();
  Sd_options.Self.debug ~dkey "%s" (Buffer.contents buf);
  Buffer.clear buf;
  printer#translated_properties()





let emitter =
  Emitter.create "StaDy" [Emitter.Property_status; Emitter.Funspec]
    ~correctness:[] ~tuning:[]













let compute_props props terms_at_Pre =
  (* Translate some parts of the pre-condition in Prolog *)
  let native_precond_generated =
    try Sd_native_precond.translate() with _ -> false in
  Sd_options.Self.feedback ~dkey:Sd_options.dkey_native_precond
    "Prolog pre-condition %s generated"
    (if native_precond_generated then "successfully" else "not");
  let kf = fst (Globals.entry_point()) in
  let translated_props =
    second_pass (Sd_options.Temp_File.get()) props terms_at_Pre in
  let test_params =
    if native_precond_generated then
      Printf.sprintf "-pc-test-params %s" (Sd_options.Precond_File.get())
    else
      ""
  in
  let cmd =
    Printf.sprintf
      "frama-c -add-path /usr/local/lib/frama-c/plugins %s -main %s -pc -pc-validate-asserts %s -pc-com %s -pc-no-xml %s"
      (Sd_options.Temp_File.get())
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
	  Unix.listen socket 1;
	  let ret = Unix.system cmd in
	  let client, _ = Unix.accept socket in
	  Sd_socket.process_socket client;
	  Sd_socket.print_exit_code ret
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
	  Unix.listen socket 1;
	  let ret = Unix.system cmd in
	  let client, _ = Unix.accept socket in
	  Sd_socket.process_socket client;
	  Sd_socket.print_exit_code ret
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
  ) translated_props









let setup_props_bijection () =
  Sd_states.Id_To_Property.clear();
  Sd_states.Property_To_Id.clear();
  (* Bijection: unique_identifier <--> property *)
  let property_id = ref 0 in
  Property_status.iter (fun property ->
    let pos1,_ = Property.location property in
    let fc_builtin = "__fc_builtin_for_normalization.i" in
    if (Filename.basename pos1.Lexing.pos_fname) <> fc_builtin then
      begin
	Sd_states.Property_To_Id.add property !property_id;
	Sd_states.Id_To_Property.add !property_id property;
	property_id := !property_id + 1
      end
  );
  let kf = fst (Globals.entry_point()) in
  let strengthened_precond =
    try
      let bhv = Sd_utils.default_behavior kf in
      let typically_preds = Sd_utils.typically_preds bhv in
      List.map (Property.ip_of_requires kf Kglobal bhv) typically_preds
    with _ -> []
  in
  List.iter Property_status.register strengthened_precond








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

      let props =
	if behaviors <> [] || functions <> [] || properties <> [] then
	  begin
	    let gather p b = List.rev_append (properties_of_behavior b) p in
	    let props = List.fold_left gather [] behaviors in
	    let gather p f = List.rev_append (properties_of_function f) p in
	    let props = List.fold_left gather props functions in
	    let gather p n = List.rev_append (properties_of_name n) p in
	    List.fold_left gather props properties
	  end
	else
	  Property_status.fold (fun p l -> p :: l) [] 
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

      
      let lengths = lengths_from_requires() in
      let terms_at_Pre = at_from_formals lengths in
      compute_props props terms_at_Pre;


      (* cleaning *)
      let clear_in = Cil_datatype.Varinfo.Hashtbl.clear in
      Datatype.String.Hashtbl.iter (fun _ tbl -> clear_in tbl) terms_at_Pre;
      Datatype.String.Hashtbl.clear terms_at_Pre;
      Datatype.String.Hashtbl.iter (fun _ tbl -> clear_in tbl) lengths;
      Datatype.String.Hashtbl.clear lengths;
      Sd_states.Id_To_Property.clear();
      Sd_states.Property_To_Id.clear()
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
  
