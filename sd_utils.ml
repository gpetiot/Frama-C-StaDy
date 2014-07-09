
(* Appends an element to the end of a list. *)
let append_end : 'a list -> 'a -> 'a list =
  fun l elt -> List.rev_append (List.rev l) [elt]

let no_repeat : 'a list -> 'a list =
  fun l ->
    let rec aux acc = function
      | [] -> acc
      | h :: t when List.mem h acc -> aux acc t
      | h :: t -> aux (h :: acc) t
    in
    aux  [] l

let fieldinfo_to_int : Cil_types.fieldinfo -> Integer.t =
  fun fi ->
    let rec aux cpt = function
      | {Cil_types.forig_name=s}::_ when s = fi.Cil_types.forig_name ->
	Integer.of_int cpt
      | _::t -> aux (cpt+1) t
      | _ -> assert false
    in
    aux 0 fi.Cil_types.fcomp.Cil_types.cfields

let machdep : unit -> int =
  fun () ->
    match Kernel.Machdep.get() with
    | "x86_64" -> 64
    | "x86_32" | "ppc_32" -> 32
    | "x86_16" -> 16
    | _ -> 32

let default_behavior : Cil_types.kernel_function -> Cil_types.funbehavior =
  fun kf ->
    List.find Cil.is_default_behavior (Annotations.behaviors kf)

let typically_preds :
    Cil_types.funbehavior -> Cil_types.identified_predicate list =
  fun bhv ->
    let typically = List.filter (fun (s,_,_) -> s = "typically")
      bhv.Cil_types.b_extended in
    let typically = List.map (fun (_,_,pred) -> pred) typically in
    List.fold_left List.rev_append [] typically

let to_id = Sd_states.Property_To_Id.find
let to_prop = Sd_states.Id_To_Property.find


open Cil_types


(* generate guards for logic vars, e.g.:
   [0 <= a <= 10; x <= b <= y]
   TODO: what is the 2nd value of the returned tuple (logic_var list) ??? *)
let rec compute_guards
    : (term*relation*logic_var*relation*term)list ->
  logic_var list ->
  predicate named ->
  ((term*relation*logic_var*relation*term)list * logic_var list) =
  fun acc vars p ->
    match p.content with
    | Pand({ content = Prel((Rlt | Rle) as r1, t11, t12) },
	   { content = Prel((Rlt | Rle) as r2, t21, t22) }) ->
      let rec terms t12 t21 = match t12.term_node, t21.term_node with
	| TLval(TVar x1, TNoOffset), TLval(TVar x2, TNoOffset) -> 
	  let v, vars = match vars with
	    | [] -> assert false
	    | v :: tl -> 
	      match v.lv_type with
	      | Ctype ty when Cil.isIntegralType ty -> v, tl
	      | Linteger -> v, tl
	      | Ltype _ as ty when Logic_const.is_boolean_type ty -> v, tl
	      | Ctype _ | Ltype _ | Lvar _ | Lreal | Larrow _ -> assert false
	  in
	  if Cil_datatype.Logic_var.equal x1 x2
	    && Cil_datatype.Logic_var.equal x1 v then
	    (t11, r1, x1, r2, t22) :: acc, vars
	  else
	    assert false
	| TLogic_coerce(_, t12), _ -> terms t12 t21 
	| _, TLogic_coerce(_, t21) -> terms t12 t21
	| TLval _, _ -> assert false
	| _, _ -> assert false
      in
      terms t12 t21
    | Pand(p1, p2) ->
      let acc, vars = compute_guards acc vars p1 in
      compute_guards acc vars p2
    | _ ->
      Sd_options.Self.feedback
	"compute_guards of %a" Printer.pp_predicate_named p;
      assert false

let error_term : term -> 'a =
  fun term ->
    match term.term_node with
    | TLogic_coerce _ -> failwith "TLogic_coerce"
    | TBinOp _ -> failwith "TBinOp"
    | Trange _ -> failwith "Trange"
    | TConst _ -> failwith "TConst"
    | TLval _ -> failwith "TLval"
    | TSizeOf _ -> failwith "TSizeOf"
    | TSizeOfE _ -> failwith "TSizeOfE"
    | TSizeOfStr _ -> failwith "TSizeOfStr"
    | TAlignOf _ -> failwith "TAlignOf"
    | TAlignOfE _ -> failwith "TAlignOfE"
    | TUnOp _ -> failwith "TUnOp"
    | TCastE _ -> failwith "TCastE"
    | TAddrOf _ -> failwith "TAddrOf"
    | TStartOf _ -> failwith "TStartOf"
    | Tapp _ -> failwith "Tapp"
    | Tlambda _ -> failwith "Tlambda"
    | TDataCons _ -> failwith "TDataCons"
    | Tif _ -> failwith "Tif"
    | Tat (_,LogicLabel(_,str)) -> Sd_options.Self.abort "Tat(_,%s)" str
    | Tbase_addr _ -> failwith "Tbase_addr"
    | Toffset _ -> failwith "Toffset"
    | Tblock_length _ -> failwith "Tblock_length"
    | TCoerce _ -> failwith "TCoerce"
    | TCoerceE _ -> failwith "TCoerceE"
    | TUpdate _ -> failwith "TUpdate"
    | Ttypeof _ -> failwith "Ttypeof"
    | Ttype _ -> failwith "Ttype"
    | Tempty_set -> failwith "Tempty_set"
    | Tunion _ -> failwith "Tunion"
    | Tinter _ -> failwith "Tinter"
    | Tcomprehension _ -> failwith "Tcomprehension"
    | Tlet _ -> failwith "Tlet"
    | _ -> Sd_options.Self.abort "term: %a" Printer.pp_term term


(* Extracts the varinfo of the variable and its inferred size as a term
   from a term t as \valid(t). *)
let rec extract_from_valid : term -> varinfo * term =
  fun t -> match t.term_node with
  | TBinOp (((PlusPI|IndexPI|MinusPI) as op),
    	    ({term_node=TCastE((TPtr _) as ty,t)} as _operand1),
    	    ({term_node=(Trange (_, Some _))} as operand2)) ->
      extract_from_valid
    	{t with term_node=TBinOp(op, {t with term_type=Ctype ty}, operand2)}
  | TBinOp((PlusPI|IndexPI),
	   ({term_node=TLval(TVar v, _)}),
	   ({term_node=
	       Trange(_,
		      Some {term_node=
			  TBinOp (MinusA, x,
				  {term_node=TConst (Integer (i, _))})})}))
      when Integer.equal i Integer.one ->
    let varinfo = Extlib.the v.lv_origin in
    varinfo, x
  | TBinOp((PlusPI|IndexPI),
	   ({term_node=TLval(TVar v, _)}),
	   ({term_node=Trange(_,Some bound)})) ->
    let varinfo = Extlib.the v.lv_origin in
    let tnode = TBinOp (PlusA, bound, Cil.lone ~loc:t.term_loc()) in
    let einfo = {exp_type=bound.term_type; exp_name=[]} in
    let term = Cil.term_of_exp_info t.term_loc tnode einfo in
    varinfo, term
  | TBinOp((PlusPI|IndexPI),
	   ({term_node=TLval(TVar v, _)}),
	   (t2 (* anything but a Trange *))) ->
    let varinfo = Extlib.the v.lv_origin in
    let tnode = TBinOp (PlusA, t2, Cil.lone ~loc:t.term_loc()) in
    let einfo = {exp_type=t2.term_type; exp_name=[]} in
    let term = Cil.term_of_exp_info t.term_loc tnode einfo in
    varinfo, term
  | TBinOp((PlusPI|IndexPI),
	   ({term_node=TLval tlval}),
	   ({term_node=
	       Trange(_,
		      Some {term_node=
			  TBinOp (MinusA, x,
				  {term_node=TConst (Integer (i, _))})})}))
      when Integer.equal i Integer.one ->
    let varinfo, _ = extract_from_valid {t with term_node=TLval tlval} in
    varinfo, x
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
  | TStartOf _ -> Sd_options.Self.abort "TStartOf \\valid(%a)" Printer.pp_term t
  | TAddrOf _ -> Sd_options.Self.abort "TAddrOf \\valid(%a)" Printer.pp_term t
  | TCoerce _ -> Sd_options.Self.abort "TCoerce \\valid(%a)" Printer.pp_term t
  | TCoerceE _ -> Sd_options.Self.abort "TCoerceE \\valid(%a)" Printer.pp_term t
  | TLogic_coerce _ ->
    Sd_options.Self.abort "TLogic_coerce \\valid(%a)" Printer.pp_term t
  | TBinOp _ -> Sd_options.Self.abort "TBinOp \\valid(%a)" Printer.pp_term t
  | _ -> Sd_options.Self.abort "\\valid(%a)" Printer.pp_term t


(* Computes and returns a hashtable such that :
   -  var1 => inferred size for var1
   -  var2 => inferred size for var2
   -  ...
   - var n => inferred size for varn *)
let lengths_from_requires :
    kernel_function -> term list Cil_datatype.Varinfo.Hashtbl.t =
  fun kf ->
    let vi = Kernel_function.get_vi kf in
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
	      let terms = append_end terms term in
	      Cil_datatype.Varinfo.Hashtbl.replace kf_tbl v terms;
	      Cil.DoChildren
	    with
	    | _ -> Cil.DoChildren
	  end
	| _ -> Cil.DoChildren
    end
    in
    let on_requires p =
      let p' = (new Sd_subst.subst)#subst_pred p.ip_content [][][][] in
      ignore (Visitor.visitFramacPredicate o p')
    in
    let on_bhv _ bhv = List.iter on_requires bhv.b_requires in
    if not (Cil.is_unused_builtin vi) then
      (* TODO: handle arrays with constant size *)
      (*Globals.Vars.iter (fun vi _ -> () );*)
      Annotations.iter_behaviors on_bhv kf;
    kf_tbl
