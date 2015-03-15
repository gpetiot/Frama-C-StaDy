
let append_end l elt = List.rev_append (List.rev l) [elt]

let no_repeat l =
  let rec aux acc = function
    | [] -> acc
    | h :: t when List.mem h acc -> aux acc t
    | h :: t -> aux (h :: acc) t
  in
  aux  [] l

let fieldinfo_to_int fi =
  let rec aux cpt = function
    | {Cil_types.forig_name=s}::_ when s = fi.Cil_types.forig_name ->
      Integer.of_int cpt
    | _::t -> aux (cpt+1) t
    | _ -> assert false
  in
  aux 0 fi.Cil_types.fcomp.Cil_types.cfields

let machdep() = match Kernel.Machdep.get() with
  | "x86_64" -> 64
  | "x86_32" | "ppc_32" -> 32
  | "x86_16" -> 16
  | _ -> 32

let default_behavior kf =
  List.find Cil.is_default_behavior (Annotations.behaviors kf)

let typically_preds bhv =
  let is_typically (s,_,_) = s = "typically" in
  let typically = List.filter is_typically bhv.Cil_types.b_extended in
  let typically = List.map (fun (_,_,pred) -> pred) typically in
  List.fold_left List.rev_append [] typically

let to_id = Sd_states.Property_To_Id.find
let to_prop = Sd_states.Id_To_Property.find


open Cil_types


(* extract guards for logic vars, e.g.: [0 <= a <= 10; x <= b <= y] *)
let extract_guards var p =
  let merge x y = match (x,y) with
    | Some x, None | None, Some x -> Some x | None, None -> None
    | _ -> assert false
  in
  let rec to_guard t = match t.term_node with
    | TLogic_coerce (_, t) -> to_guard t
    | TLval(TVar x, TNoOffset) -> Cil_datatype.Logic_var.equal x var
    | _ -> false
  in
  let rec aux p = match p.content with
    | Pand(p1, p2) ->
      let a,b,c,d = aux p1 and e,f,g,h = aux p2 in
      merge a e, merge b f, merge c g, merge d h
    | Prel((Rlt|Rle) as r, t, u) when to_guard t -> None, None, Some r, Some u
    | Prel((Rlt|Rle) as r, t, u) when to_guard u -> Some t, Some r, None, None
    | Prel(Rge, t, u) when to_guard t -> Some u, Some Rle, None, None
    | Prel(Rgt, t, u) when to_guard t -> Some u, Some Rlt, None, None
    | Prel(Rge, t, u) when to_guard u -> None, None, Some Rle, Some t
    | Prel(Rgt, t, u) when to_guard u -> None, None, Some Rlt, Some t
    | _ -> None, None, None, None
  in
  let a,b,c,d = aux p in
  Extlib.the a, Extlib.the b, Extlib.the c, Extlib.the d


let error_term t = Options.Self.abort "term: %a" Sd_debug.pp_term t
let error_toffset t = Options.Self.abort "toffset: %a" Sd_debug.pp_toffset t
let error_pred p = Options.Self.abort "pred: %a" Sd_debug.pp_pred p

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
  | _ -> Options.Self.debug "\\valid(%a)" Sd_debug.pp_term t; assert false


(* Computes and returns a hashtable such that :
   -  var1 => inferred size for var1
   -  var2 => inferred size for var2
   -  ...
   - var n => inferred size for varn *)
let lengths_from_requires kf =
  let vi = Kernel_function.get_vi kf in
  let kf_tbl = Cil_datatype.Varinfo.Hashtbl.create 32 in
  let o = object
    inherit Visitor.frama_c_inplace

    method! vpredicate_named p =
      if List.mem "rte" p.name then Cil.SkipChildren else Cil.DoChildren

    method! vpredicate = function
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
    let p' = (new Sd_subst.subst ())#id_pred p [][][][] in
    ignore (Visitor.visitFramacIdPredicate o p')
  in
  let on_bhv _ bhv = List.iter on_requires bhv.b_requires in
  if not (Cil.is_unused_builtin vi) then Annotations.iter_behaviors on_bhv kf;
  kf_tbl

let mpz_t() =
  let ty = Options.mpz_t in
  let ty = !ty in
  let ty = Extlib.the ty in
  ty

let print_counter_examples
      gui (pprint:('a, Format.formatter, unit) format -> 'a) prop =
  let file_tbl = Sd_states.Counter_examples.find prop in
  let print x = if gui then pprint "%s@.@\n" x else pprint " %s@\n" x in
  let n_chars n str =
    let size = let s = n - (String.length str) in if s < 0 then 0 else s in
    if (String.length str > n) then
      let size_1, size_2 =
	if n mod 2 = 0 then (n - 3) / 2 + 1, (n - 3) / 2
	else (n - 3) / 2, (n - 3) / 2
      in
      (String.sub str 0 size_1)^"..."
      ^(String.sub str ((String.length str) - size_2) size_2)
    else (String.make size ' ') ^ str
  in
  let n_chars = n_chars 17 in
  let on_var var (input,conc,symb) =
    print
      (Printf.sprintf
	 "%s|%s|%s|%s"
	 (n_chars var) (n_chars input) (n_chars conc) (n_chars symb))
  in
  let on_file f var_tbl =
    Format.fprintf
      Format.str_formatter "Counter-example for @[%a@]@." Property.pretty prop;
    print (Format.flush_str_formatter());
    if f <> "" then print (Printf.sprintf "%s\n" f);
    if (Datatype.String.Hashtbl.length var_tbl) > 0 then
      print (Printf.sprintf
	       "%s|%s|%s|%s"
	       (n_chars "variable") (n_chars "input")
	       (n_chars "concrete output") (n_chars "symbolic output"));
    Datatype.String.Hashtbl.iter_sorted on_var var_tbl
  in
  let to_list t = Datatype.String.Hashtbl.fold (fun k v l -> (k,v)::l) t [] in
  let only i to_do l =
    let rec aux cpt = function
      | (k,v) :: t when cpt < i -> to_do k v; aux (cpt+1) t
      | _ -> ()
    in
    aux 0 l
  in
  only 1 on_file (to_list file_tbl)

(* unused: interpreting string as precondition predicates *)
(* let type_str_precond kf pred_as_string = *)
(*   let module M = Logic_typing.Make(struct *)
(*     let is_loop() = false *)
(*     let anonCompFieldName = Cabs2cil.anonCompFieldName *)
(*     let conditionalConversion = Cabs2cil.logicConditionalConversion *)
(*     let find_macro _ = raise Not_found *)
(*     let find_var x = *)
(*       let vi = *)
(* 	try Globals.Vars.find_from_astinfo x (VLocal kf) *)
(* 	with Not_found -> *)
(* 	  try Globals.Vars.find_from_astinfo x (VFormal kf) *)
(* 	  with Not_found -> Globals.Vars.find_from_astinfo x VGlobal *)
(*       in *)
(*       Cil.cvar_to_lvar vi *)
(*     let find_enum_tag x = *)
(*       try Globals.Types.find_enum_tag x *)
(*       with Not_found -> failwith ("Unbound variable " ^ x) *)
(*     let find_type = Globals.Types.find_type *)
(*     let find_comp_field info s = Field(Cil.getCompField info s,NoOffset) *)
(*     let find_label s = Kernel_function.find_label kf s *)

(*     let remove_logic_function = Logic_env.remove_logic_function *)
(*     let remove_logic_type = Logic_env.remove_logic_type *)
(*     let remove_logic_ctor = Logic_env.remove_logic_ctor *)

(*     let add_logic_function = Logic_utils.add_logic_function *)
(*     let add_logic_type = Logic_env.add_logic_type *)
(*     let add_logic_ctor = Logic_env.add_logic_ctor *)

(*     let find_all_logic_functions = Logic_env.find_all_logic_functions *)
(*     let find_logic_type = Logic_env.find_logic_type *)
(*     let find_logic_ctor = Logic_env.find_logic_ctor *)

(*     let integral_cast ty t = *)
(*       failwith *)
(*         (Pretty_utils.sfprintf *)
(*            "term %a has type %a, but %a is expected." *)
(*            Printer.pp_term t *)
(* 	   Printer.pp_logic_type Linteger Printer.pp_typ ty) *)
(*   end) *)
(*   in *)
(*   let lenv = Logic_typing.Lenv.empty() in *)
(*   let _, lexpr = Logic_lexer.lexpr (Lexing.dummy_pos, pred_as_string) in *)
(*   M.predicate lenv lexpr *)
