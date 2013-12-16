
open Cil
open Cil_types
open Lexing



type at_term =
| Quantif_term of
    logic_var
  * term (* borne min *)
  * term (* borne max *)
  * at_term
| Unquantif_term of term





let rec str_at_term = function
  | Unquantif_term t -> Pretty_utils.sfprintf "%a" Printer.pp_term t
  | Quantif_term(v,t1,t2,a) ->
    Pretty_utils.sfprintf "%s[%a,%a,%a]"
      (str_at_term a)
      Printer.pp_logic_var v
      Printer.pp_term t1
      Printer.pp_term t2

let rec compareat x y = str_at_term x = str_at_term y






class subst = object(self)

  method subst_pred
    pred
    (labels:(logic_label*logic_label)list)
    (args:(logic_var*term)list)
    (quantifs:(logic_var*logic_var)list) =
    match pred with
    | Pfalse -> Pfalse
    | Ptrue -> Ptrue
    | Papp (li,lassoc,params) ->
      let new_labels =
	List.map (fun (x,y) -> x, self#subst_label y labels) lassoc in
      let new_args = List.map2 (fun x y -> x,y) li.l_profile params in
      let new_args =
	List.map (fun (x,y) ->
	  x, self#subst_term y labels args quantifs) new_args in
      begin
	match li.l_body with
	| LBnone -> Options.Self.not_yet_implemented "LBnone"
	| LBreads _ -> Options.Self.not_yet_implemented "LBreads"
	| LBterm _ -> Options.Self.not_yet_implemented "LBterm"
	| LBpred {content=p} -> self#subst_pred p new_labels new_args quantifs
	| LBinductive _ -> Options.Self.not_yet_implemented "LBinductive"
      end
    | Pseparated t -> Pseparated t
    | Prel (rel,t1,t2) -> Prel (rel,
				self#subst_term t1 labels args quantifs,
				self#subst_term t2 labels args quantifs)
    | Pand (p1, p2) -> Pand (self#subst_pnamed p1 labels args quantifs,
			     self#subst_pnamed p2 labels args quantifs)
    | Por (p1, p2) -> Por (self#subst_pnamed p1 labels args quantifs,
			   self#subst_pnamed p2 labels args quantifs)
    | Pxor (p1, p2) -> Pxor (self#subst_pnamed p1 labels args quantifs,
			     self#subst_pnamed p2 labels args quantifs)
    | Pimplies (p1, p2) -> Pimplies (self#subst_pnamed p1 labels args quantifs,
				     self#subst_pnamed p2 labels args quantifs)
    | Piff (p1, p2) -> Piff (self#subst_pnamed p1 labels args quantifs,
			     self#subst_pnamed p2 labels args quantifs)
    | Pnot p -> Pnot (self#subst_pnamed p labels args quantifs)
    | Pif (t,p1,p2) -> Pif (self#subst_term t labels args quantifs,
			    self#subst_pnamed p1 labels args quantifs,
			    self#subst_pnamed p2 labels args quantifs)
    | Plet (v,p) -> Plet (v, self#subst_pnamed p labels args quantifs)
    | Pforall (q,p) ->
      let q' = List.map (fun v -> {v with lv_name = "__q_" ^ v.lv_name}) q in
      let q'' = List.combine q q' in
      Pforall(q',self#subst_pnamed p labels args (List.rev_append q'' quantifs))
    | Pexists (q,p) ->
      let q' = List.map (fun v -> {v with lv_name = "__q_" ^ v.lv_name}) q in
      let q'' = List.combine q q' in
      Pexists (q,self#subst_pnamed p labels args (List.rev_append q'' quantifs))
    | Pat (p,l) -> Pat (self#subst_pnamed p labels args quantifs,
			self#subst_label l labels)
    | Pvalid_read (l,t) -> Pvalid_read (self#subst_label l labels,
					self#subst_term t labels args quantifs)
    | Pvalid (l,t) -> Pvalid (self#subst_label l labels,
			      self#subst_term t labels args quantifs)
    | Pinitialized (l,t) -> Pinitialized(self#subst_label l labels,
					 self#subst_term t labels args quantifs)
    | Pallocable (l,t) -> Pallocable (self#subst_label l labels,
				      self#subst_term t labels args quantifs)
    | Pfreeable (l,t) -> Pfreeable (self#subst_label l labels,
				    self#subst_term t labels args quantifs)
    | Pfresh (l1,l2,t1,t2) -> Pfresh (self#subst_label l1 labels,
				      self#subst_label l2 labels,
				      self#subst_term t1 labels args quantifs,
				      self#subst_term t2 labels args quantifs)
    | Psubtype (t1,t2) -> Psubtype (self#subst_term t1 labels args quantifs,
				    self#subst_term t2 labels args quantifs)
      
  method subst_label l labels =
    if List.mem_assoc l labels then List.assoc l labels else l

  method subst_tnode term labels args quantifs =
    match term with
    | TConst c -> TConst c
    | TLval (TVar v,y) ->
      let off = self#subst_toffset y labels args quantifs in
      if List.mem_assoc v args then
	let t' = List.assoc v args in
	match t'.term_node with
	| TLval v' -> TLval (Logic_const.addTermOffsetLval off v')
	| _ as whatever -> assert (off = TNoOffset); whatever
      else
	if List.mem_assoc v quantifs then
	  TLval (TVar (List.assoc v quantifs), off)
	else
	  TLval (TVar v, off)
    | TLval(TResult t,y) -> TLval(TResult t,
				  self#subst_toffset y labels args quantifs)
    | TLval(TMem t,y) -> TLval(TMem (self#subst_term t labels args quantifs),
			       self#subst_toffset y labels args quantifs)
    | TSizeOf t -> TSizeOf t
    | TSizeOfE t -> TSizeOfE (self#subst_term t labels args quantifs)
    | TSizeOfStr s -> TSizeOfStr s
    | TAlignOf t -> TAlignOf t
    | TAlignOfE t -> TAlignOfE (self#subst_term t labels args quantifs)
    | TUnOp (u,t) -> TUnOp (u, self#subst_term t labels args quantifs)
    | TBinOp (b,t1,t2) -> TBinOp (b,
				  self#subst_term t1 labels args quantifs,
				  self#subst_term t2 labels args quantifs)
    | TCastE (ty,t) -> TCastE (ty, self#subst_term t labels args quantifs)
    | TAddrOf _ -> Options.Self.not_yet_implemented "TAddrOf"
    | TStartOf _ -> Options.Self.not_yet_implemented "TStartOf"
    | Tapp (li,lassoc,params) ->
      let new_labels =
	List.map (fun (x,y) -> x, self#subst_label y labels) lassoc in
      let new_args = List.map2 (fun x y -> x,y) li.l_profile params in
      let new_args =
	List.map (fun (x,y) ->
	  x, self#subst_term y labels args quantifs) new_args in
      begin
	match li.l_body with
	| LBnone -> Options.Self.not_yet_implemented "LBnone"
	| LBreads _ -> Options.Self.not_yet_implemented "LBreads"
	| LBterm{term_node=t} -> self#subst_tnode t new_labels new_args quantifs
	| LBpred _ -> Options.Self.not_yet_implemented "LBpred"
	| LBinductive _ -> Options.Self.not_yet_implemented "LBinductive"
      end
    | Tlambda (q,t) -> Tlambda (q, self#subst_term t labels args quantifs)
    | TDataCons _ -> Options.Self.not_yet_implemented "TDataCons"
    | Tif (t1,t2,t3) -> Tif (self#subst_term t1 labels args quantifs,
			     self#subst_term t2 labels args quantifs,
			     self#subst_term t3 labels args quantifs)
    | Tat (t,l) -> Tat (self#subst_term t labels args quantifs,
			self#subst_label l labels)
    | Tbase_addr (l,t) -> Tbase_addr (self#subst_label l labels,
				      self#subst_term t labels args quantifs)
    | Toffset (l,t) -> Toffset (self#subst_label l labels,
				self#subst_term t labels args quantifs)
    | Tblock_length(l,t)-> Tblock_length(self#subst_label l labels,
					 self#subst_term t labels args quantifs)
    | Tnull -> Tnull
    | TLogic_coerce(y,t)-> TLogic_coerce(y,
					 self#subst_term t labels args quantifs)
    | TCoerce (t, ty) -> TCoerce (self#subst_term t labels args quantifs, ty)
    | TCoerceE (t1, t2) -> TCoerceE (self#subst_term t1 labels args quantifs,
				     self#subst_term t2 labels args quantifs)
    | TUpdate (t1,o,t2) -> TUpdate (self#subst_term t1 labels args quantifs,
				    self#subst_toffset o labels args quantifs,
				    self#subst_term t2 labels args quantifs)
    | Ttypeof t -> Ttypeof (self#subst_term t labels args quantifs)
    | Ttype t -> Ttype t
    | Tempty_set -> Tempty_set
    | Tunion l->Tunion(List.map(fun x->self#subst_term x labels args quantifs)l)
    | Tinter l->Tinter(List.map(fun x->self#subst_term x labels args quantifs)l)
    | Tcomprehension (t,q,None) ->
      Tcomprehension (self#subst_term t labels args quantifs, q, None)
    | Tcomprehension (t,q,Some p) ->
      Tcomprehension (self#subst_term t labels args quantifs, q,
		      Some (self#subst_pnamed p labels args quantifs))
    | Trange (None, None) -> Trange (None, None)
    | Trange(None,Some t)-> Trange(None,
				   Some(self#subst_term t labels args quantifs))
    | Trange(Some t,None)-> Trange(Some(self#subst_term t labels args quantifs),
				   None)
    | Trange (Some t1, Some t2) ->
      Trange (Some(self#subst_term t1 labels args quantifs),
	      Some(self#subst_term t2 labels args quantifs))
    | Tlet (v,t) -> Tlet (v, self#subst_term t labels args quantifs)

  method subst_toffset offset labels args quantifs =
    match offset with
    | TNoOffset -> TNoOffset
    | TField (f,o) -> TField (f, self#subst_toffset o labels args quantifs)
    | TModel (m,o) -> TModel (m, self#subst_toffset o labels args quantifs)
    | TIndex (t,o) -> TIndex (self#subst_term t labels args quantifs,
			      self#subst_toffset o labels args quantifs)

  method subst_term t labels args quantifs =
    { t with term_node = self#subst_tnode t.term_node labels args quantifs }

  method subst_pnamed p labels args quantifs =
    { p with content = self#subst_pred p.content labels args quantifs }
end




class rm_at = object
  inherit Visitor.frama_c_inplace

  method! vterm term =
    let f x = match x.term_node with Tat(t,_) -> t | _ -> x in
    ChangeDoChildrenPost (term, f)
end



let result_involved term =
  let ret = ref false in
  let o = object
    inherit Visitor.frama_c_inplace

    method! vterm t =
      match t.term_node with
      | TLval (TResult _, _) -> ret := true; SkipChildren
      | _ when !ret -> SkipChildren
      | _ -> DoChildrenPost (fun x -> x)
  end in
  ignore (Visitor.visitFramacTerm o term);
  !ret



class find_bounds = object(self)
  inherit Visitor.frama_c_inplace

  val mutable in_quantif = false
  val upper_bounds : term Cil_datatype.Logic_var.Hashtbl.t =
    Cil_datatype.Logic_var.Hashtbl.create 32
  val lower_bounds : term Cil_datatype.Logic_var.Hashtbl.t =
    Cil_datatype.Logic_var.Hashtbl.create 32
    
  method! vpredicate pred =
    let add_if_result_not_involved hashtbl v t =
	if(result_involved t) then
	  Options.Self.debug ~dkey:Options.dkey_first_pass
	    "\\result involved in %a, not added as bound of \\at-term"
	    Printer.pp_term t
	else
	  Cil_datatype.Logic_var.Hashtbl.add hashtbl v t
    in
    match pred with
    | Papp _ -> failwith "no application after substitution"
    | Pat _ -> Options.Self.not_yet_implemented "Pat"
    | Prel (Rle,{term_node=TLval(TVar v,TNoOffset)},t)
    | Prel (Rge,t,{term_node=TLval(TVar v,TNoOffset)}) when in_quantif ->
      add_if_result_not_involved upper_bounds v t;
      DoChildrenPost (fun x -> x)
    | Prel (Rge,{term_node=TLval(TVar v,TNoOffset)},t)
    | Prel (Rle,t,{term_node=TLval(TVar v,TNoOffset)}) when in_quantif ->
      add_if_result_not_involved lower_bounds v t;
      DoChildrenPost (fun x -> x)
    | Prel (Rlt,{term_node=TLval(TVar v,TNoOffset)},t)
    | Prel (Rgt,t,{term_node=TLval(TVar v,TNoOffset)}) when in_quantif ->
      let exp_info = Cil.exp_info_of_term t in
      let tnode = TBinOp (MinusA, t, Cil.lone()) in
      let t' = Cil.term_of_exp_info t.term_loc tnode exp_info in
      add_if_result_not_involved upper_bounds v t';
      DoChildrenPost (fun x -> x)
    | Prel (Rgt,{term_node=TLval(TVar v,TNoOffset)},t)
    | Prel (Rlt,t,{term_node=TLval(TVar v,TNoOffset)}) when in_quantif ->
      let exp_info = Cil.exp_info_of_term t in
      let tnode = TBinOp (PlusA, t, Cil.lone()) in
      let t' = Cil.term_of_exp_info t.term_loc tnode exp_info in
      add_if_result_not_involved lower_bounds v t';
      DoChildrenPost (fun x -> x)
    | Pforall (_,{content=Pimplies _})
    | Pexists (_,{content=Pand _}) ->
      in_quantif <- true;
      DoChildrenPost (fun x -> in_quantif <- false; x)
    | Pforall _ -> Options.Self.not_yet_implemented
      "unsupported: try \\forall ... => ... instead"
    | Pexists _ -> Options.Self.not_yet_implemented
      "unsupported: try \\exists ... && ... instead"
    | _ -> DoChildrenPost (fun x -> x)

  val terms_at_Pre : (at_term list) Datatype.String.Hashtbl.t =
    Datatype.String.Hashtbl.create 32
  val terms_at_stmt : (at_term list) Cil_datatype.Stmt.Hashtbl.t =
    Cil_datatype.Stmt.Hashtbl.create 32

  method get_terms_at_Pre = terms_at_Pre
  method get_terms_at_stmt = terms_at_stmt

  method! vterm _t =
    let find_or_abort hashtbl v =
      try Cil_datatype.Logic_var.Hashtbl.find hashtbl v
      with _ ->
	Options.Self.abort "logic var %a unbounded" Printer.pp_logic_var v
    in
    let construct lv att =
      let lower = find_or_abort lower_bounds lv in
      let upper = find_or_abort upper_bounds lv in
      let lower = Visitor.visitFramacTerm (new rm_at) lower in
      let upper = Visitor.visitFramacTerm (new rm_at) upper in
      (Quantif_term (lv, lower, upper, att))
    in
    let f x =
      match x.term_node with
      | Tat (t, StmtLabel stmt) ->
	Options.Self.debug ~dkey:Options.dkey_first_pass
	  "AT: \\at(%a,?) StmtLabel" Printer.pp_term t; 
	let terms =
	  try Cil_datatype.Stmt.Hashtbl.find terms_at_stmt !stmt
	  with _ -> []
	in
	let lvars = Cil.extract_free_logicvars_from_term t in
	let lvars = Cil_datatype.Logic_var.Set.filter
	  (fun x -> x.lv_origin = None) lvars in
	begin
	  try
	    let at_term =
	      let t = Visitor.visitFramacTerm (new rm_at) t in
	      Cil_datatype.Logic_var.Set.fold construct lvars (Unquantif_term t)
	    in
	    let terms = at_term :: terms in
	    Cil_datatype.Stmt.Hashtbl.replace terms_at_stmt !stmt terms
	  with
	  | _ -> Options.Self.debug ~dkey:Options.dkey_first_pass
	    "unbounded logic var: term %a not added in terms_at_stmt"
	    Printer.pp_term t
	end;
	x
      | Tat (t, LogicLabel(_stmtopt,label)) ->
	Options.Self.debug ~dkey:Options.dkey_first_pass
	  "AT: \\at(%a,%s) LogicLabel" Printer.pp_term t label;
	begin
	  try
	    let func = (Extlib.the self#current_func).svar.vname in
	    if label = "Pre" || label = "Old" then
	      begin
		let terms =
		  try Datatype.String.Hashtbl.find terms_at_Pre func
		  with _ -> []
		in
		let lvars = Cil.extract_free_logicvars_from_term t in
		let lvars = Cil_datatype.Logic_var.Set.filter
		  (fun x -> x.lv_origin = None) lvars in
		begin
		  try
		    let at_term =
		      let t' = Visitor.visitFramacTerm (new rm_at) t in
		      Cil_datatype.Logic_var.Set.fold
			construct lvars (Unquantif_term t')
		    in
		    let terms = at_term :: terms in
		    Datatype.String.Hashtbl.replace terms_at_Pre func terms
		  with
		  | _ -> Options.Self.debug ~dkey:Options.dkey_first_pass
		    "unbounded logic var: term %a not added in terms_at_Pre"
		    Printer.pp_term t
		end
	      end
	    else
	      Options.Self.not_yet_implemented "AT: Tat (?, other label)"
	  with _ -> ()
	end;
	x
      | _ -> x
    in
    if result_involved _t then
      begin
	Options.Self.debug ~dkey:Options.dkey_first_pass
	  "\\result involved in %a, \\at-term ignored"
	  Printer.pp_term _t;
	DoChildrenPost (fun x -> x)
      end
    else
      DoChildrenPost f
end









let first_pass() =
  let dkey = Options.dkey_first_pass in
  let terms_at_Pre : (at_term list) Datatype.String.Hashtbl.t =
    Datatype.String.Hashtbl.create 32 in
  let terms_at_stmt : (at_term list) Cil_datatype.Stmt.Hashtbl.t =
    Cil_datatype.Stmt.Hashtbl.create 32 in
  
  let o = object(self)
    inherit Visitor.frama_c_inplace

    (* builtin functions ignored *)
    method! vglob_aux g =
      let f x = x in
      match g with
      | GFun(fundec,_) when Cil.is_unused_builtin fundec.svar -> SkipChildren
      | GVar(vi,_,_) when Cil.is_unused_builtin vi -> SkipChildren
      | GVarDecl(_,vi,_) when Cil.is_unused_builtin vi -> SkipChildren
      | GAnnot _ -> SkipChildren
      | _ -> DoChildrenPost f

    method! vpredicate_named pred =
      let c = new subst in
      let p' = c#subst_pred pred.content [] [] [] in
      Options.Self.debug ~dkey "avant: %a" Printer.pp_predicate pred.content;
      Options.Self.debug ~dkey "après: %a" Printer.pp_predicate p';
      Options.Self.debug ~dkey "===============================";
      let fb = new find_bounds in
      if self#current_func = None then
	fb#reset_current_func()
      else
	fb#set_current_func  (Extlib.the self#current_func);
      ignore (Visitor.visitFramacPredicate (fb :> Visitor.frama_c_inplace) p');
      Datatype.String.Hashtbl.iter (fun k v ->
	let t = try Datatype.String.Hashtbl.find terms_at_Pre k with _ -> [] in
	let v' =
	  let rec aux ret = function
	    | [] -> ret
	    | x::s-> aux(if List.exists(compareat x) ret then ret else x::ret) s
	  in
	  aux [] v
	in
	let v' = List.filter (fun x -> not (List.exists (compareat x) t)) v' in
	let new_terms = List.rev_append t v' in
	Datatype.String.Hashtbl.replace terms_at_Pre k new_terms
      ) fb#get_terms_at_Pre;
      Cil_datatype.Stmt.Hashtbl.iter (fun k v ->
	let t = try Cil_datatype.Stmt.Hashtbl.find terms_at_stmt k with _->[] in
	let v' =
	  let rec aux ret = function
	    | [] -> ret
	    | x::s-> aux(if List.exists(compareat x) ret then ret else x::ret) s
	  in
	  aux [] v
	in
	let v' = List.filter (fun x -> not (List.exists (compareat x) t)) v' in
	let new_terms = List.rev_append t v' in
	Cil_datatype.Stmt.Hashtbl.replace terms_at_stmt k new_terms
      ) fb#get_terms_at_stmt;
      SkipChildren
  end
  in
  Visitor.visitFramacFile o (Ast.get());
  terms_at_Pre, terms_at_stmt








(* outputs the AST of a project in a file *)
let print_in_file filename props =
  Kernel.Unicode.set false;

  (* first pass: prepare the quantifiers predicates, ignore the output *)
  let fmt = Format.make_formatter (fun _ _ _ -> ()) ignore in
  let module First_pass = Printer_builder.Make
	(struct class printer =
		  Pcva_printer.pcva_printer props ~first_pass:true end)
  in
  First_pass.pp_file fmt (Ast.get());

  (* second pass: print the instrumented quantif, output in a file *)
  let out = open_out filename in
  let fmt = Format.formatter_of_out_channel out in
    let module Second_pass = Printer_builder.Make
	(struct class printer =
		  Pcva_printer.pcva_printer props ~first_pass:false end)
  in
  Second_pass.pp_file fmt (Ast.get());
  flush out;
  close_out out;

  (* cleaning *)
  Pcva_printer.quantif_pred_cpt := 0;
  Queue.clear Pcva_printer.quantif_pred_queue;
  Pcva_printer.postcond := None;
  Pcva_printer.at_term_cpt := 0;
  Datatype.String.Hashtbl.clear Pcva_printer.at_term_affect_in_function;
  Cil_datatype.Stmt.Hashtbl.clear Pcva_printer.at_term_affect_in_stmt



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
      let terms_at_Pre, terms_at_stmt = first_pass() in

      Options.Self.debug ~dkey:Options.dkey_first_pass "R: terms_at_Pre:";
      Datatype.String.Hashtbl.iter_sorted (fun f terms ->
	Options.Self.debug ~dkey:Options.dkey_first_pass "R: function '%s'" f;
	List.iter (fun x -> Options.Self.debug ~dkey:Options.dkey_first_pass
	  "R: %s" (str_at_term x)) terms;
	Options.Self.debug ~dkey:Options.dkey_first_pass "R: ----------------"
      ) terms_at_Pre;

      Options.Self.debug ~dkey:Options.dkey_first_pass "R: terms_at_stmt:";
      Cil_datatype.Stmt.Hashtbl.iter_sorted (fun stmt terms ->
	Options.Self.debug ~dkey:Options.dkey_first_pass
	  "R: stmt %a" Printer.pp_stmt stmt;
	List.iter (fun x -> Options.Self.debug ~dkey:Options.dkey_first_pass
	  "R: %s" (str_at_term x)) terms
      ) terms_at_stmt;

      Datatype.String.Hashtbl.clear terms_at_Pre;
      Cil_datatype.Stmt.Hashtbl.clear terms_at_stmt;


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
  
