
open Cil_types


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
    | Plet (li,{content=p}) ->
      let lv = li.l_var_info in
      begin
	match li.l_body with
	| LBnone -> Options.Self.not_yet_implemented "LBnone"
	| LBreads _ -> Options.Self.not_yet_implemented "LBreads"
	| LBterm t' ->
	  let t'' = self#subst_term t' labels args quantifs in
	  self#subst_pred p labels ((lv,t'')::args) quantifs
	| LBpred _ -> Options.Self.not_yet_implemented "LBpred"
	| LBinductive _ -> Options.Self.not_yet_implemented "LBinductive"
      end
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
    | Tlet (li,{term_node=t}) ->
      let lv = li.l_var_info in
      begin
	match li.l_body with
	| LBnone -> Options.Self.not_yet_implemented "LBnone"
	| LBreads _ -> Options.Self.not_yet_implemented "LBreads"
	| LBterm t' ->
	  let t'' = self#subst_term t' labels args quantifs in
	  self#subst_tnode t labels ((lv,t'')::args) quantifs
	| LBpred _ -> Options.Self.not_yet_implemented "LBpred"
	| LBinductive _ -> Options.Self.not_yet_implemented "LBinductive"
      end

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
