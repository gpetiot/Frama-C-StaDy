
open Cil_types

type env = {
  label_assoc : (logic_label * logic_label) list;
  term_assoc : (logic_var * term) list;
  pred_assoc : (logic_var * predicate) list;
  var_assoc : (logic_var * logic_var) list;
}

let empty_env = {label_assoc=[]; term_assoc=[]; pred_assoc=[]; var_assoc=[];}

let label env l =
  if List.mem_assoc l env.label_assoc then List.assoc l env.label_assoc else l

let rec app env li lassoc params =
  let rec aux_label ret = function
    | [] -> ret
    | (x,y)::t -> aux_label ((x, label env y)::ret) t
  in
  let rec aux_arg ret = function
    | [], [] -> ret
    | x::t1, y::t2 -> aux_arg ((x, term env y)::ret) (t1,t2)
    | _ -> assert false
  in
  {env with label_assoc=aux_label [] lassoc;
	    term_assoc=aux_arg [] (li.l_profile, params);}

and pred env = function
  | Pfalse -> Pfalse
  | Ptrue -> Ptrue
  | Papp(l,_,_) when List.mem_assoc l.l_var_info env.pred_assoc ->
     List.assoc l.l_var_info env.pred_assoc
  | Papp (li,lassoc,params) as pred' ->
    let new_env = app env li lassoc params in
    begin
      match li.l_body with
      | LBnone -> pred' (* TODO *)
      | LBreads _ -> pred' (* TODO *)
      | LBterm _ -> assert false (* unreachable *)
      | LBpred {content=p} -> pred new_env p
      | LBinductive _ -> pred' (* TODO *)
    end
  | Pseparated t -> Pseparated (List.map (fun x -> term env x) t)
  | Prel(rel,t1,t2) -> Prel(rel, term env t1, term env t2)
  | Pand(p1,p2) -> Pand(pnamed env p1, pnamed env p2)
  | Por(p1,p2) -> Por (pnamed env p1, pnamed env p2)
  | Pxor(p1,p2) -> Pxor(pnamed env p1, pnamed env p2)
  | Pimplies(p1,p2) -> Pimplies(pnamed env p1, pnamed env p2)
  | Piff(p1,p2) -> Piff(pnamed env p1, pnamed env p2)
  | Pnot p -> Pnot (pnamed env p)
  | Pif (t,p1,p2) -> Pif (term env t, pnamed env p1, pnamed env p2)
  | Plet (li,{content=p}) as pred' ->
    let lv = li.l_var_info in
    begin
      match li.l_body with
      | LBnone -> pred' (* TODO *)
      | LBreads _ -> pred' (* TODO *)
      | LBterm t' ->
	 pred {env with term_assoc=((lv,(term env t'))::env.term_assoc)} p
      | LBpred {content=x} ->
	 pred {env with pred_assoc=((lv,pred env x)::env.pred_assoc)} p
      | LBinductive _ -> pred' (* TODO *)
    end
  | Pforall (q,p)
  | Pexists (q,p) as pred' ->
    let prefix v = {v with lv_name = "__q_" ^ v.lv_name} in
    let rec aux ret1 ret2 = function
      | [] -> ret1,ret2
      | h::t -> aux ((prefix h)::ret1) ((h, prefix h)::ret2) t
    in
    let new_q, new_quantifs = aux [] [] q in
    let new_quantifs = List.rev_append new_quantifs env.var_assoc in
    let env = {env with var_assoc=new_quantifs} in
    let new_p = pnamed env p in
    begin
      match pred' with
      | Pforall _ -> Pforall (new_q, new_p)
      | _ -> Pexists (new_q, new_p)
    end
  | Pat (p,l) -> Pat (pnamed env p, label env l)
  | Pvalid_read (l,t) -> Pvalid_read (label env l, term env t)
  | Pvalid (l,t) -> Pvalid (label env l, term env t)
  | Pinitialized (l,t) -> Pinitialized(label env l, term env t)
  | Pdangling (l,t) -> Pdangling(label env l, term env t)
  | Pallocable (l,t) -> Pallocable (label env l, term env t)
  | Pfreeable (l,t) -> Pfreeable (label env l, term env t)
  | Pfresh(l1,l2,t1,t2) -> Pfresh(label env l1, label env l2,
				  term env t1, term env t2)
  | Psubtype(t1,t2) -> Psubtype (term env t1, term env t2)

and tnode env = function
  | TConst c -> TConst c
  | TLval (TVar v,y) ->
     let off = toffset env y in
     if List.mem_assoc v env.term_assoc then
       let t' = List.assoc v env.term_assoc in
       match t'.term_node with
       | TLval v' -> TLval (Logic_const.addTermOffsetLval off v')
       | whatever -> assert (off = TNoOffset); whatever
     else
       TLval (TVar (if List.mem_assoc v env.var_assoc then
		      List.assoc v env.var_assoc else v), off)
  | TLval(TResult t,y) -> TLval(TResult t, toffset env y)
  | TLval(TMem t,y) -> TLval(TMem(term env t), toffset env y)
  | TSizeOf t -> TSizeOf t
  | TSizeOfE t -> TSizeOfE (term env t)
  | TSizeOfStr s -> TSizeOfStr s
  | TAlignOf t -> TAlignOf t
  | TAlignOfE t -> TAlignOfE (term env t)
  | TUnOp (u,t) -> TUnOp (u, term env t)
  | TBinOp(b,t1,t2) -> TBinOp(b, term env t1, term env t2)
  | TCastE (ty,t) -> TCastE (ty, term env t)
  | TAddrOf _ as term' -> term' (* TODO *)
  | TStartOf _ as term' -> term' (* TODO *)
  | Tapp (li,[],[lower;upper;({term_node=Tlambda([_],_)} as lambda)]) ->
    Tapp (li,[],List.map (fun x -> term env x) [lower; upper; lambda])
  | Tapp (li,lassoc,params) as term' ->
    let env = app env li lassoc params in
    let new_terms = List.map (fun t -> term env t) params in
    begin
      match li.l_body with
      | LBnone ->
	 let s = li.l_var_info.lv_name in
	 if s = "\\cos" || s = "\\abs" || s = "\\sqrt" || s = "\\pow" then
	   Tapp(li,env.label_assoc,new_terms)
	 else term' (* TODO *)
      | LBreads _ -> term' (* TODO *)
      | LBterm {term_node = t} -> tnode env t
      | LBpred _ -> assert false (* unreachable *)
      | LBinductive _ -> term' (* TODO *)
    end
  | Tlambda (q,t) -> Tlambda (q, term env t)
  | TDataCons _ as term' -> term' (* TODO *)
  | Tif(t1,t2,t3) -> Tif(term env t1, term env t2, term env t3)
  | Tat (t,l) -> Tat (term env t, label env l)
  | Tbase_addr (l,t) -> Tbase_addr (label env l, term env t)
  | Toffset (l,t) -> Toffset (label env l, term env t)
  | Tblock_length(l,t)-> Tblock_length(label env l, term env t)
  | Tnull -> Tnull
  | TLogic_coerce(y,t)-> TLogic_coerce(y, term env t)
  | TCoerce (t, ty) -> TCoerce (term env t, ty)
  | TCoerceE(t1, t2) -> TCoerceE(term env t1, term env t2)
  | TUpdate(t1,o,t2) -> TUpdate(term env t1, toffset env o, term env t2)
  | Ttypeof t -> Ttypeof (term env t)
  | Ttype t -> Ttype t
  | Tempty_set -> Tempty_set
  | Tunion l -> Tunion (List.map (fun x -> term env x) l)
  | Tinter l -> Tinter (List.map (fun x -> term env x) l)
  | Tcomprehension (t,q,None) -> Tcomprehension(term env t, q, None)
  | Tcomprehension _ as term' -> term'
  | Trange(None, None) -> Trange(None, None)
  | Trange(None,Some t)-> Trange(None, Some(term env t))
  | Trange(Some t,None)-> Trange(Some(term env t), None)
  | Trange(Some t1, Some t2) -> Trange(Some(term env t1), Some(term env t2))
  | Tlet (li,{term_node=t}) as term' ->
    let lv = li.l_var_info in
    match li.l_body with
    | LBnone -> term' (* TODO *)
    | LBreads _ -> term' (* TODO *)
    | LBterm t' ->
       tnode {env with term_assoc=((lv, (term env t'))::env.term_assoc)} t
    | LBpred _ -> assert false (* unreachable *)
    | LBinductive _ -> term' (* TODO *)

and toffset env = function
  | TNoOffset -> TNoOffset
  | TField (f,o) -> TField (f, toffset env o)
  | TModel (m,o) -> TModel (m, toffset env o)
  | TIndex (t,o) -> TIndex (term env t, toffset env o)

and term env t = {t with term_node=tnode env t.term_node}

and pnamed env p = {p with content=pred env p.content}

and id_pred env p = {p with ip_content=pred env p.ip_content}

(* exported functions *)

let pred p = pred empty_env p
let pnamed p = pnamed empty_env p
let id_pred p = id_pred empty_env p
