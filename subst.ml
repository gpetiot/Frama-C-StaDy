
open Cil_types


let label l ll = if List.mem_assoc l ll then List.assoc l ll else l

let rec app ll vt vv li lassoc params =
  let rec aux_label ret = function
    | [] -> ret
    | (x,y)::t -> aux_label ((x, label y ll)::ret) t
  in
  let rec aux_arg ret = function
    | [], [] -> ret
    | x::t1, y::t2 -> aux_arg ((x, term y ll vt vv)::ret) (t1,t2)
    | _ -> assert false
  in
  aux_label [] lassoc, aux_arg [] (li.l_profile, params)

and pred pred' ll vt vp vv = match pred' with
  | Pfalse -> Pfalse
  | Ptrue -> Ptrue
  | Papp(l,_,_) when List.mem_assoc l.l_var_info vp ->List.assoc l.l_var_info vp
  | Papp (li,lassoc,params) ->
    let new_labels, new_args = app ll vt vv li lassoc params in
    begin
      match li.l_body with
      | LBnone -> pred' (* TODO *)
      | LBreads _ -> pred' (* TODO *)
      | LBterm _ -> assert false (* unreachable *)
      | LBpred {content=p} -> pred p new_labels new_args vp vv
      | LBinductive _ -> pred' (* TODO *)
    end
  | Pseparated t -> Pseparated (List.map (fun x -> term x ll vt vv) t)
  | Prel(rel,t1,t2) -> Prel(rel, term t1 ll vt vv, term t2 ll vt vv)
  | Pand(p1,p2) -> Pand(pnamed p1 ll vt vp vv,pnamed p2 ll vt vp vv)
  | Por(p1,p2) -> Por (pnamed p1 ll vt vp vv, pnamed p2 ll vt vp vv)
  | Pxor(p1,p2) -> Pxor(pnamed p1 ll vt vp vv,pnamed p2 ll vt vp vv)
  | Pimplies(p1,p2) -> Pimplies(pnamed p1 ll vt vp vv, pnamed p2 ll vt vp vv)
  | Piff(p1,p2) -> Piff(pnamed p1 ll vt vp vv,pnamed p2 ll vt vp vv)
  | Pnot p -> Pnot (pnamed p ll vt vp vv)
  | Pif (t,p1,p2) -> Pif (term t ll vt vv, pnamed p1 ll vt vp vv,
			  pnamed p2 ll vt vp vv)
  | Plet (li,{content=p}) ->
    let lv = li.l_var_info in
    begin
      match li.l_body with
      | LBnone -> pred' (* TODO *)
      | LBreads _ -> pred' (* TODO *)
      | LBterm t' -> pred p ll ((lv,(term t' ll vt vv))::vt) vp vv
      | LBpred {content=x} -> pred p ll vt ((lv,pred x ll vt vp vv)::vp) vv
      | LBinductive _ -> pred' (* TODO *)
    end
  | Pforall (q,p) | Pexists(q,p) ->
    let prefix v = {v with lv_name = "__q_" ^ v.lv_name} in
    let rec aux ret1 ret2 = function
      | [] -> ret1,ret2
      | h::t -> aux ((prefix h)::ret1) ((h, prefix h)::ret2) t
    in
    let new_q, new_quantifs = aux [] [] q in
    let new_quantifs = List.rev_append new_quantifs vv in
    let new_p = pnamed p ll vt vp new_quantifs in
    begin
      match pred' with
      | Pforall _ -> Pforall (new_q, new_p)
      | _ -> Pexists (new_q, new_p)
    end
  | Pat (p,l) -> Pat (pnamed p ll vt vp vv, label l ll)
  | Pvalid_read (l,t) -> Pvalid_read (label l ll, term t ll vt vv)
  | Pvalid (l,t) -> Pvalid (label l ll, term t ll vt vv)
  | Pinitialized (l,t) -> Pinitialized(label l ll, term t ll vt vv)
  | Pdangling (l,t) -> Pdangling(label l ll, term t ll vt vv)
  | Pallocable (l,t) -> Pallocable (label l ll, term t ll vt vv)
  | Pfreeable (l,t) -> Pfreeable (label l ll, term t ll vt vv)
  | Pfresh(l1,l2,t1,t2) -> Pfresh(label l1 ll,label l2 ll,
				  term t1 ll vt vv,term t2 ll vt vv)
  | Psubtype(t1,t2) -> Psubtype (term t1 ll vt vv, term t2 ll vt vv)

and tnode term' ll vt vv = match term' with
  | TConst c -> TConst c
  | TLval (TVar v,y) ->
     let off = toffset y ll vt vv in
     if List.mem_assoc v vt then
       let t' = List.assoc v vt in
       match t'.term_node with
       | TLval v' -> TLval (Logic_const.addTermOffsetLval off v')
       | whatever -> assert (off = TNoOffset); whatever
     else TLval (TVar (if List.mem_assoc v vv then List.assoc v vv else v), off)
  | TLval(TResult t,y) -> TLval(TResult t, toffset y ll vt vv)
  | TLval(TMem t,y) -> TLval(TMem(term t ll vt vv),toffset y ll vt vv)
  | TSizeOf t -> TSizeOf t
  | TSizeOfE t -> TSizeOfE (term t ll vt vv)
  | TSizeOfStr s -> TSizeOfStr s
  | TAlignOf t -> TAlignOf t
  | TAlignOfE t -> TAlignOfE (term t ll vt vv)
  | TUnOp (u,t) -> TUnOp (u, term t ll vt vv)
  | TBinOp(b,t1,t2) -> TBinOp(b, term t1 ll vt vv, term t2 ll vt vv)
  | TCastE (ty,t) -> TCastE (ty, term t ll vt vv)
  | TAddrOf _ -> term' (* TODO *)
  | TStartOf _ -> term' (* TODO *)
  | Tapp (li,[],[lower;upper;({term_node=Tlambda([_],_)} as lambda)]) ->
    Tapp (li,[],List.map (fun x -> term x ll vt vv) [lower; upper; lambda])
  | Tapp (li,lassoc,params) ->
    let new_labels, new_args = app ll vt vv li lassoc params in
    let new_terms = List.map (fun x -> term x ll vt vv) params in
    begin
      match li.l_body with
      | LBnone ->
	 let s = li.l_var_info.lv_name in
	 if s = "\\cos" || s = "\\abs" || s = "\\sqrt" || s = "\\pow" then
	   Tapp(li,new_labels,new_terms)
	 else term' (* TODO *)
      | LBreads _ -> term' (* TODO *)
      | LBterm {term_node = t} -> tnode t new_labels new_args vv
      | LBpred _ -> assert false (* unreachable *)
      | LBinductive _ -> term' (* TODO *)
    end
  | Tlambda (q,t) -> Tlambda (q, term t ll vt vv)
  | TDataCons _ -> term' (* TODO *)
  | Tif(t1,t2,t3) -> Tif(term t1 ll vt vv, term t2 ll vt vv, term t3 ll vt vv)
  | Tat (t,l) -> Tat (term t ll vt vv, label l ll)
  | Tbase_addr (l,t) -> Tbase_addr (label l ll, term t ll vt vv)
  | Toffset (l,t) -> Toffset (label l ll, term t ll vt vv)
  | Tblock_length(l,t)-> Tblock_length(label l ll, term t ll vt vv)
  | Tnull -> Tnull
  | TLogic_coerce(y,t)-> TLogic_coerce(y, term t ll vt vv)
  | TCoerce (t, ty) -> TCoerce (term t ll vt vv, ty)
  | TCoerceE(t1, t2) -> TCoerceE(term t1 ll vt vv, term t2 ll vt vv)
  | TUpdate(t1,o,t2) -> TUpdate(term t1 ll vt vv,toffset o ll vt vv,
				term t2 ll vt vv)
  | Ttypeof t -> Ttypeof (term t ll vt vv)
  | Ttype t -> Ttype t
  | Tempty_set -> Tempty_set
  | Tunion l -> Tunion (List.map (fun x -> term x ll vt vv) l)
  | Tinter l -> Tinter (List.map (fun x -> term x ll vt vv) l)
  | Tcomprehension (t,q,None) -> Tcomprehension(term t ll vt vv, q, None)
  | Tcomprehension _ -> term'
  | Trange(None, None) -> Trange(None, None)
  | Trange(None,Some t)-> Trange(None, Some(term t ll vt vv))
  | Trange(Some t,None)-> Trange(Some(term t ll vt vv), None)
  | Trange(Some t1, Some t2) ->
     Trange(Some(term t1 ll vt vv), Some(term t2 ll vt vv))
  | Tlet (li,{term_node=t}) ->
    let lv = li.l_var_info in
    match li.l_body with
    | LBnone -> term' (* TODO *)
    | LBreads _ -> term' (* TODO *)
    | LBterm t' -> tnode t ll ((lv, (term t' ll vt vv))::vt) vv
    | LBpred _ -> assert false (* unreachable *)
    | LBinductive _ -> term' (* TODO *)

and toffset offset ll vt vv = match offset with
  | TNoOffset -> TNoOffset
  | TField (f,o) -> TField (f, toffset o ll vt vv)
  | TModel (m,o) -> TModel (m, toffset o ll vt vv)
  | TIndex (t,o) -> TIndex (term t ll vt vv, toffset o ll vt vv)

and term t ll vt vv = {t with term_node=tnode t.term_node ll vt vv}

and pnamed p ll vt vp vv = {p with content=pred p.content ll vt vp vv}

and id_pred p ll vt vp vv = {p with ip_content=pred p.ip_content ll vt vp vv}
