
  method! vinst = function
  | Call (_ret, fct_exp, args, _loc) ->
    begin
      try
	let subst_o = new Sd_subst.subst in
	let fct_varinfo = match fct_exp.enode  with
	  | Lval(Var v,NoOffset) -> v
	  | _ -> assert false
	in
	let kf = Globals.Functions.get fct_varinfo in
	let formals = Kernel_function.get_formals kf in
	let formals = List.map Cil.cvar_to_lvar formals in
	let params = List.map (Logic_utils.expr_to_term ~cast:false) args in
	let vt = List.combine formals params in
	let subst p = subst_o#pred p [] vt [] [] in
	let is_def = Kernel_function.is_definition kf in
	let to_ctype = function Ctype t -> t | _ -> assert false in
	if not is_def then
	  begin
	    let on_behavior _ b =
	      let to_prop = Property.ip_of_requires kf Kglobal b in
	      let do_requires pred =
		let prop = to_prop pred in
		let id = Sd_utils.to_id prop in
		self#pc_assert_exception
		  (subst pred.ip_content) "Pre-condition!" id prop
	      in
	      let do_ensures pred =
	      	let inserts_0, var = self#predicate (subst pred.ip_content) in
	      	let insert_1 = Instru(Pc_assume var) in
	      	inserts_0 @ [insert_1]
	      in
	      let glob_decl, ins_before =
		let globals_saved =
		  Globals.Vars.fold (fun v _ ins ->
		    let inserts_d, inserts_b, inserts_a =
		      self#save_varinfo kf v in
		    ins @ inserts_d @ inserts_b @ inserts_a
		  ) []
		in
		let args_saved =
		  List.fold_left (fun l (lv, t) ->
		    let var_name = "arg_" ^ lv.lv_name in
		    let ty = to_ctype t.term_type in
		    let var = My_ctype_var (ty, var_name) in
		    let i_0 = Decl_ctype_var var in
		    let i',x = self#term t in
		    let i_1 = Instru (Affect (var, self#ctype_fragment x)) in
		    l @ i' @ [i_0 ; i_1]
		  ) [] vt
		in
		let saves = globals_saved @ args_saved in

		if b.b_requires <> [] then
		  let inserts = List.map do_requires b.b_requires in
		  let inserts = List.fold_left (@) [] inserts in

		  if b.b_assumes <> [] then
		    let inserts_0, exp =
		      self#cond_of_assumes ~subst_pred:subst b.b_assumes in
		    let insert_1 = If(exp, inserts, []) in
		    [], saves @ inserts @ inserts_0 @ [insert_1]
		  else [], saves @ inserts
		else [], saves
	      in
	      let stmt = Extlib.the self#current_stmt in
	      List.iter (self#insert Glob) glob_decl;
	      List.iter (self#insert (BegStmt stmt.sid)) ins_before
	    in
	    Annotations.iter_behaviors on_behavior kf
	  end;
      with _ -> ()
    end;
    Cil.DoChildren
  | _ -> Cil.DoChildren
