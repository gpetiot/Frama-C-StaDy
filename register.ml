
open Cil
open Cil_types
open Lexing



let print_strtbl_vartbl_terms hashtbl dkey =
  Options.Self.debug ~dkey "========================";
  Datatype.String.Hashtbl.iter_sorted (fun f tbl ->
    Options.Self.debug ~dkey "function '%s'" f;
    Cil_datatype.Varinfo.Hashtbl.iter_sorted (fun v ts ->
      Options.Self.debug ~dkey "var '%s'" v.vname;
      List.iter (fun t -> Options.Self.debug ~dkey "%a " Printer.pp_term t) ts
    ) tbl;
    Options.Self.debug ~dkey "----------------"
  ) hashtbl;
  Options.Self.debug ~dkey "========================"




(* Appends an element to the end of a list. *)
let append_end : 'a list -> 'a -> 'a list =
  fun l elt -> List.rev_append (List.rev l) [elt]





(* Extracts the varinfo of the variable and its inferred size as a term
   from a term t as \valid(t). *)
let extract_from_valid : term -> varinfo * term =
  fun t -> match t with
  | {term_node=TBinOp((PlusPI|IndexPI),
		      ({term_node=TLval(TVar v, _)} as _t1),
		      ({term_node=Trange(_,Some bound)} as _t2))} ->
    let varinfo = Extlib.the v.lv_origin in
    let tnode = TBinOp (PlusA, bound, Cil.lone ~loc:t.term_loc()) in
    let einfo = {exp_type=bound.term_type; exp_name=[]} in
    let term = Cil.term_of_exp_info t.term_loc tnode einfo in
    varinfo, term

  | {term_node=TBinOp((PlusPI|IndexPI),
		      ({term_node=TLval(TVar v, _)} as _t1),
		      (t2 (* anything but a Trange *)))} ->
    let varinfo = Extlib.the v.lv_origin in
    let tnode = TBinOp (PlusA, t2, Cil.lone ~loc:t.term_loc()) in
    let einfo = {exp_type=t2.term_type; exp_name=[]} in
    let term = Cil.term_of_exp_info t.term_loc tnode einfo in
    varinfo, term

  | {term_node=TLval(TVar v, _)} ->
    let varinfo = Extlib.the v.lv_origin in
    let term = Cil.lone ~loc:t.term_loc () in
    varinfo, term

  | _ ->
    Options.Self.debug ~dkey:Options.dkey_lengths
      "\\valid(%a) ignored" Printer.pp_term t;
    assert false



(* Computes and returns a hashtable such that :
   function_name1 =>
      var1 => inferred size for var1
      var2 => inferred size for var2
   function_name2 =>
       ...
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

	  Annotations.iter_behaviors (fun _ bhv ->
	    List.iter (fun id_pred ->
	      let pred = id_pred.ip_content in
	      let c = new Sd_subst.subst in
	      let pred = c#subst_pred pred [] [] [] in

	      let o = object
		inherit Visitor.frama_c_inplace

		method! vpredicate p =
		  match p with
		  | Pvalid(_, t) | Pvalid_read(_, t) ->
		    begin
		      try
			let varinfo, term = extract_from_valid t in
			let terms =
			  try Cil_datatype.Varinfo.Hashtbl.find kf_tbl varinfo
			  with Not_found -> []
			in
			let terms = append_end terms term in
			Cil_datatype.Varinfo.Hashtbl.replace
			  kf_tbl varinfo terms;
			DoChildren
		      with
		      | _ -> DoChildren
		    end
		  | _ -> DoChildren
	      end
	      in
	      
	      ignore (Visitor.visitFramacPredicate o pred)
	    ) bhv.b_requires
	  ) kf;
	  Datatype.String.Hashtbl.add lengths kf_name kf_tbl
	end
    );
    Options.Self.debug ~dkey:Options.dkey_lengths "LENGTHS:";
    print_strtbl_vartbl_terms lengths Options.dkey_lengths;
    lengths





(* Computes and returns a hashtable such that :
   function_name1 =>
      formal var1 => size of var1 saved
      formal var2 => size of var2 saved
   function_name2 =>
       ...
*)
let at_from_formals :
    term list Cil_datatype.Varinfo.Hashtbl.t Datatype.String.Hashtbl.t
    -> term list Cil_datatype.Varinfo.Hashtbl.t Datatype.String.Hashtbl.t =
  fun lengths ->
    let terms_at_Pre = Datatype.String.Hashtbl.create 32 in
    Globals.Functions.iter (fun kf ->
      let vi = Kernel_function.get_vi kf in
      if not (Cil.is_unused_builtin vi) then
	begin
	  let kf_name = Kernel_function.get_name kf in
	  let kf_tbl = Cil_datatype.Varinfo.Hashtbl.create 32 in
	  let lengths_tbl = Datatype.String.Hashtbl.find lengths kf_name in
	  let formals = Kernel_function.get_formals kf in
	  List.iter (fun vi ->
	    let terms =
	      try Cil_datatype.Varinfo.Hashtbl.find lengths_tbl vi
	      with Not_found -> []
	    in
	    Cil_datatype.Varinfo.Hashtbl.add kf_tbl vi terms
	  ) formals;
	  Datatype.String.Hashtbl.add terms_at_Pre kf_name kf_tbl
	end
    );
    Options.Self.debug ~dkey:Options.dkey_at "AT:";
    print_strtbl_vartbl_terms terms_at_Pre Options.dkey_at;
    terms_at_Pre







let debug_builtins = Kernel.register_category "printer:builtins"
let print_var v =
  not (Cil.is_unused_builtin v) || Kernel.is_debug_key_enabled debug_builtins
let no_repeat l : 'a list =
  let rec aux acc = function
    | [] -> acc
    | h :: t when List.mem h acc -> aux acc t
    | h :: t -> aux (h :: acc) t
  in
  aux  [] l
(* to change a \valid to a pathcrawler_dimension *)
(* term -> term * term *)
let rec extract_terms t : term * term =
  let loc = t.term_loc in
  match t.term_node with
  | TLval _ -> t, lzero ~loc ()
  | TCastE (_,term)
  | TCoerce (term,_)
  | TAlignOfE term -> extract_terms term
  | TBinOp (PlusPI,x,{term_node = Trange(_,Some y)})
  | TBinOp (IndexPI,x,{term_node = Trange(_,Some y)}) -> x,y
  | TBinOp ((PlusPI|IndexPI),x,y) -> x,y
  | TBinOp (MinusPI,x,y) ->
    x, term_of_exp_info loc (TUnOp(Neg,y)) {exp_type=t.term_type; exp_name=[]}
  | TStartOf _ -> t, lzero ~loc ()
  | TAddrOf (TVar _, TIndex _) ->
    let lv = mkTermMem t TNoOffset in
    let te = term_of_exp_info loc(TLval lv){exp_type=t.term_type;exp_name=[]} in
    extract_terms te
  | _ -> Options.Self.not_yet_implemented "term: %a" Printer.pp_term t






class second_pass_printer props terms_at_Pre () = object(self)
  inherit Printer.extensible_printer () as super

  val mutable pred_cpt = 0
  val pred_assoc : int Cil_datatype.Identified_predicate.Hashtbl.t =
    Cil_datatype.Identified_predicate.Hashtbl.create 32
  val mutable postcond = None
  val mutable result_varinfo = None
  val mutable current_function = None
    
  method private in_current_function vi =
    assert (current_function = None);
    current_function <- Some vi

  method private out_current_function =
    assert (current_function <> None);
    current_function <- None

(*
  method! term_node fmt t =
    let ctyp = function | Ctype t->t | Linteger->longType | _ -> assert false in
    match t.term_node with
    | TConst(Integer(i,_)) ->
      if (Integer.to_string i) = "-2147483648" then
	Format.fprintf fmt "(-2147483647-1)"
      else
	super#term_node fmt t
    | Tat(_, StmtLabel _) -> failwith "\\at on stmt label unsupported!"
    | Tat(term,LogicLabel(_,stringlabel)) ->
      if ignore_at then
	self#term fmt term
      else
      begin
	if stringlabel = "Old" then
	  if first_pass then
	    begin
	      match self#current_stmt with
	      | None ->
		begin
		  let fct_name = try (Extlib.the last_function).vname
		    with _ ->
		      failwith
			(Pretty_utils.sfprintf
			   "no current function (term: %a)"
			   Printer.pp_term t)
		  in
		  Options.Self.debug ~dkey:Options.dkey_old_printer
		    "fct_name = %s" fct_name;
		  let affects = try
				  Datatype.String.Hashtbl.find
				    at_term_affect_in_function fct_name
		    with _ ->
		      Options.Self.debug ~dkey:Options.dkey_old_printer
			"fct %s queue created" fct_name;
		      Queue.create()
		  in
		  Queue.add (fun fmt ->
		    Format.fprintf fmt "%a = %a;@\n"
		      (self#typ
			 (Some (fun fmt -> Format.fprintf fmt "term_at_%i"
			   !at_term_cpt)))
		      (ctyp term.term_type)
		      self#term
		      term
		  ) affects;
		  Options.Self.debug ~dkey:Options.dkey_old_printer
		    "add at fct %s -> ..." fct_name;
		  Datatype.String.Hashtbl.add
		    at_term_affect_in_function fct_name affects
		end
	      | Some stmt ->
		begin
		  let affects = try
				  Cil_datatype.Stmt.Hashtbl.find
				    at_term_affect_in_stmt stmt
		    with _ ->
		      Options.Self.debug ~dkey:Options.dkey_old_printer
			"stmt queue created";
		      Queue.create()
		  in
		  Queue.add (fun fmt ->
		    Format.fprintf fmt "%a = %a;@\n"
		      (self#typ
			 (Some (fun fmt -> Format.fprintf fmt "term_at_%i"
			   !at_term_cpt)))
		      (ctyp term.term_type)
		      self#term
		      term
		  ) affects;
		  Options.Self.debug ~dkey:Options.dkey_old_printer
		    "add at stmt ?? -> ...";
		  Cil_datatype.Stmt.Hashtbl.add
		    at_term_affect_in_stmt stmt affects
		end
	    end
	  else
	    begin
	      Format.fprintf fmt "term_at_%i" !at_term_cpt;
	      at_term_cpt := !at_term_cpt + 1
	    end
	else
	  failwith (Printf.sprintf "\\at label '%s' unsupported!"
		      stringlabel)
      end
    | _ -> super#term_node fmt t
*)
end



let second_pass filename props terms_at_Pre =
  ignore props;
  Kernel.Unicode.set false;
  let out = open_out filename in
  let fmt = Format.formatter_of_out_channel out in
  let module P =
	Printer_builder.Make
	  (struct class printer =
		    second_pass_printer props terms_at_Pre end) in
  P.pp_file fmt (Ast.get());
  flush out;
  close_out out




let pcva_emitter =
  Emitter.create "StaDyPlus" [Emitter.Property_status; Emitter.Funspec]
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
  ()
(*
  (* Translate some parts of the pre-condition in Prolog *)
  Native_precond.translate();
  Options.Self.feedback ~dkey:Options.dkey_native_precond
    "Prolog precondition successfully generated";
  let parameters_file = Options.Precond_File.get () in
  Options.Self.feedback ~dkey:Options.dkey_native_precond
    "The result is in file %s" parameters_file;
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
      "frama-c -add-path /usr/local/lib/frama-c/plugins %s -main %s -pc -pc-validate-asserts %s -pc-com %s -pc-no-xml %s"
      (Options.Temp_File.get())
      (Kernel_function.get_name (fst(Globals.entry_point())))
      test_params
      (Options.Socket_Type.get())
      (Options.PathCrawler_Options.get())
  in
  Options.Self.debug ~dkey:Options.dkey_socket "cmd: %s" cmd;
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
	  Options.Self.feedback ~dkey:Options.dkey_socket
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
	  Pcva_socket.process_socket client;
	  Pcva_socket.print_exit_code ret
	with _ ->
	  Unix.close socket;
	  Options.Self.feedback ~dkey:Options.dkey_socket
	    "error: internet socket now closed!"
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
  Options.Self.result "all-paths: %b" !Prop_id.all_paths;
  Options.Self.result "%i test cases" (States.NbCases.get());
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
      if !Prop_id.all_paths && (not !Prop_id.typically) then
	Property_status.emit pcva_emitter ~hyps prop ~distinct status
  ) translated_properties;
  Prop_id.translated_properties := [];
  Prop_id.all_paths := false;
  Prop_id.typically := false
*)   





let properties_of_behavior name =
  Globals.Functions.fold (fun kf props ->
    Annotations.fold_behaviors (fun _ b p ->
      if b.b_name = name then
	List.rev_append (Property.ip_all_of_behavior kf Kglobal b) p
      else
	p
    ) kf props
  ) []



let properties_of_function name =
  let props = ref [] in
  Globals.Functions.iter (fun kf ->
    let kf_name = Kernel_function.get_name kf in
    if kf_name = name then
      begin
	Annotations.iter_behaviors (fun _ bhv ->
	  let new_props = Property.ip_all_of_behavior kf Kglobal bhv in
	  props := List.rev_append new_props !props
	) kf;
	let o = object
	  inherit Visitor.frama_c_inplace
	  method! vstmt_aux stmt =
	    let f s =
	      Annotations.iter_code_annot (fun _ ca ->
		let p = Property.ip_of_code_annot kf s ca in
		props := List.rev_append p !props
	      ) s;
	      s
	    in
	    ChangeDoChildrenPost(stmt, f)
	end in
	try
	  let fundec = Kernel_function.get_definition kf in
	  ignore (Visitor.visitFramacFunction o fundec)
	with _ -> ()
      end
  );
  !props



let properties_of_name name =
  let props = ref [] in
  Globals.Functions.iter (fun kf ->
    Annotations.iter_behaviors (fun _ bhv ->
      List.iter (fun id_pred ->
	if List.mem name id_pred.ip_name then
	  let p = Property.ip_of_requires kf Kglobal bhv id_pred in
	  props := p :: !props
      ) bhv.b_requires;
      List.iter (fun (tk,id_pred) ->
	if List.mem name id_pred.ip_name then
	  let p = Property.ip_of_ensures kf Kglobal bhv (tk,id_pred) in
	  props := p :: !props
      ) bhv.b_post_cond;
    ) kf;
    let o = object
      inherit Visitor.frama_c_inplace
      method! vstmt_aux stmt =
	let f s =
	  Annotations.iter_code_annot (fun _ ca ->
	    match ca.annot_content with
	    | AAssert(_,{name=l})
	    | AInvariant(_,_,{name=l}) ->
	      if List.mem name l then
		let p = Property.ip_of_code_annot kf s ca in
		props := List.rev_append p !props
	    | AStmtSpec(_,{spec_behavior=bhvs}) ->
	      List.iter (fun b ->
		List.iter (fun id_pred ->
		  if List.mem name id_pred.ip_name then
		    let p = Property.ip_of_requires kf (Kstmt s) b id_pred in
		    props := p :: !props
		) b.b_requires;
		List.iter (fun (tk,id_pred) ->
		  if List.mem name id_pred.ip_name then
		    let p =
		      Property.ip_of_ensures kf (Kstmt s) b (tk,id_pred) in
		    props := p :: !props
		) b.b_post_cond;
	      ) bhvs
	    | _ -> ()
	  ) s;
	  s
	in
	ChangeDoChildrenPost(stmt, f)
    end in
    try
      let fundec = Kernel_function.get_definition kf in
      ignore (Visitor.visitFramacFunction o fundec)
    with _ -> ()
  );
  !props




let run() =
  if Options.Enabled.get() then
    begin
      setup_props_bijection();
      let properties = Options.Properties.get () in
      let behaviors = Options.Behaviors.get () in
      let functions = Options.Functions.get () in

      let props =
	if behaviors <> [] || functions <> [] || properties <> [] then
	  begin
	    let gather p b = List.rev_append (properties_of_behavior b) p in
	    let bhv_props = List.fold_left gather [] behaviors in
	    let gather p f = List.rev_append (properties_of_function f) p in
	    let fct_props = List.fold_left gather [] functions in
	    let gather p n = List.rev_append (properties_of_name n) p in
	    let nam_props = List.fold_left gather [] properties in
	    List.rev_append bhv_props (List.rev_append fct_props nam_props)
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


      Options.Self.debug ~dkey:Options.dkey_properties "selected properties:";
      List.iter (fun p ->
	try
	  let id = Prop_id.to_id p in
	  Options.Self.debug ~dkey:Options.dkey_properties
	    "%a (%i) found" Property.pretty p id
	with _ -> Options.Self.debug ~dkey:Options.dkey_properties
	  "%a not found" Property.pretty p
      ) props;

      (*compute_props props;*)
      let lengths = lengths_from_requires() in
      let terms_at_Pre = at_from_formals lengths in

      
      second_pass (Options.Temp_File.get()) props terms_at_Pre;    


      (* cleaning *)
      let clear_in = Cil_datatype.Varinfo.Hashtbl.clear in
      Datatype.String.Hashtbl.iter (fun _ tbl -> clear_in tbl) terms_at_Pre;
      Datatype.String.Hashtbl.clear terms_at_Pre;
      Datatype.String.Hashtbl.iter (fun _ tbl -> clear_in tbl) lengths;
      Datatype.String.Hashtbl.clear lengths;
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
  
