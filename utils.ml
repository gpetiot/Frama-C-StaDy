
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

let comma : string -> string -> string =
  fun x y -> if x = "" then y else (x ^ ", " ^ y)

let fold_comma : string list -> string =
  fun l -> List.fold_left comma "" l

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

open Cil_types

(* to change a \valid to a pathcrawler_dimension *)
let rec extract_terms : term -> term * term =
  fun t ->
    let loc = t.term_loc in
    match t.term_node with
    | TLval _ -> t, Cil.lzero ~loc ()
    | TCastE (_,term)
    | TCoerce (term,_)
    | TAlignOfE term -> extract_terms term
    | TBinOp ((PlusPI|IndexPI),x,{term_node = Trange(_,Some y)}) -> x,y
    | TBinOp ((PlusPI|IndexPI),x,y) -> x,y
    | TBinOp (MinusPI,x,y) ->
      let einfo = {exp_type=t.term_type; exp_name=[]} in
      x, Cil.term_of_exp_info loc (TUnOp(Neg,y)) einfo
    | TStartOf _ -> t, Cil.lzero ~loc ()
    | TAddrOf (TVar _, TIndex _) ->
      let lv = Cil.mkTermMem t TNoOffset in
      let einfo = {exp_type=t.term_type;exp_name=[]} in
      let te = Cil.term_of_exp_info loc(TLval lv) einfo in
      extract_terms te
    | _ -> Options.Self.not_yet_implemented "term: %a" Printer.pp_term t

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
      Options.Self.feedback "compute_guards of %a" Printer.pp_predicate_named p;
      assert false
