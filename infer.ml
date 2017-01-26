
open Cil_types

let append_end l elt = List.rev_append (List.rev l) [elt]

let is_one = function
  | {term_node=TConst(Integer(i,_))} when Integer.equal i Integer.one -> true
  | _ -> false


(* Extracts the varinfo of the variable and its inferred size as a term
   from a term t as \valid(t). *)
let rec extract_from_valid t =
  let loc = t.term_loc in
  match t.term_node with
  | TBinOp ((PlusPI|IndexPI|MinusPI) as op,
    	    {term_node=TCastE((TPtr _) as ty,t)},
    	    ({term_node=(Trange (_, Some _))} as operand2)) ->
    extract_from_valid
      {t with term_node=TBinOp(op, {t with term_type=Ctype ty}, operand2)}
  | TBinOp((PlusPI|IndexPI),
	   {term_node=TLval(TVar {lv_origin=Some varinfo}, _)},
	   {term_node=Trange(_,Some {term_node=TBinOp(MinusA,x,k)})})
      when is_one k ->
    varinfo, x
  | TBinOp((PlusPI|IndexPI),
	   {term_node=TLval(TVar {lv_origin=Some varinfo}, _)},
	   {term_node=Trange(_,Some bound)}) ->
    let tnode = TBinOp (PlusA, bound, Cil.lone ~loc ()) in
    let einfo = {exp_type=bound.term_type; exp_name=[]} in
    varinfo, Cil.term_of_exp_info t.term_loc tnode einfo
  | TBinOp((PlusPI|IndexPI),{term_node=TLval(TVar{lv_origin=Some vi}, _)},t2) ->
    let tnode = TBinOp (PlusA, t2, Cil.lone ~loc ()) in
    let einfo = {exp_type=t2.term_type; exp_name=[]} in
    vi, Cil.term_of_exp_info t.term_loc tnode einfo
  | TBinOp((PlusPI|IndexPI),
	   {term_node=TLval tlval},
	   {term_node=Trange(_,Some {term_node=TBinOp(MinusA,x,k)})})
      when is_one k ->
    let varinfo, _ = extract_from_valid {t with term_node=TLval tlval} in
    varinfo, x
  | TBinOp((PlusPI|IndexPI),
	   {term_node=TLval tlval},
	   {term_node=Trange(_,Some bound)}) ->
    let tnode = TBinOp (PlusA, bound, Cil.lone ~loc ()) in
    let einfo = {exp_type=bound.term_type; exp_name=[]} in
    let term = Cil.term_of_exp_info t.term_loc tnode einfo in
    let varinfo, _ = extract_from_valid {t with term_node=TLval tlval} in
    varinfo, term
  | TLval (TVar{lv_origin=Some vi},TNoOffset) -> vi, Cil.lone ~loc ()
  | TLval (TMem m, TNoOffset) ->
    let varinfo, _ = extract_from_valid m in
    varinfo, Cil.lone ~loc ()
  | TAddrOf (TMem x, TIndex (y, TNoOffset)) ->
     let x' = Cil.mkTermMem ~addr:x ~off:TNoOffset in
     let rec type_of_pointed = function
       | Ctype (TPtr (ty,_)) -> Ctype ty
       | Ctype (TArray (ty,_,_,_)) -> Ctype ty
       | Ctype (TNamed (x,_)) -> type_of_pointed (Ctype x.ttype)
       | ty ->
	  Options.abort
	    ~current:true "unsupported type %a" Printer.pp_logic_type ty
     in
     let ty = type_of_pointed (Cil.typeOfTermLval x') in
     let x' = Logic_const.term (TLval x') ty in
     extract_from_valid {t with term_node=(TBinOp(PlusPI,x',y))}
  | _ -> Options.debug "\\valid(%a)" Debug.pp_term t; assert false


let lengths_from_requires kf =
  let vi = Kernel_function.get_vi kf in
  let kf_tbl = Cil_datatype.Varinfo.Hashtbl.create 32 in
  let o = object
    inherit Visitor.frama_c_inplace

    method! vpredicate p =
      if List.mem "rte" p.pred_name then Cil.SkipChildren else Cil.DoChildren

    method! vpredicate_node = function
    | Pvalid(_, t) | Pvalid_read(_, t) ->
      begin
	try
	  let v, term = extract_from_valid t in
	  let terms =
	    try Cil_datatype.Varinfo.Hashtbl.find kf_tbl v
	    with Not_found -> []
	  in
	  let terms = append_end terms term in
	  Cil_datatype.Varinfo.Hashtbl.replace kf_tbl v terms;
	  Cil.DoChildren
	with _ -> Cil.DoChildren
      end
    | _ -> Cil.DoChildren
  end
  in
  let on_requires p =
    let p' = Inline.id_pred p in
    ignore (Visitor.visitFramacIdPredicate o p')
  in
  let on_bhv _ bhv = List.iter on_requires bhv.b_requires in
  if not (Cil.is_unused_builtin vi) then Annotations.iter_behaviors on_bhv kf;
  kf_tbl
