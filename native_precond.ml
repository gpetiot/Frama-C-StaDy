
open Cil
open Cil_types
open Lexing


let output chan str =
  Options.Self.debug ~level:2 "%s" str;
  output_string chan str
    

let typically_typer ~typing_context ~loc bhv ps =
  match ps with
  | p::[] ->
    bhv.b_extended <-
      ("typically",42,
       [Logic_const.new_predicate 
           (typing_context.Logic_typing.type_predicate 
	      (typing_context.Logic_typing.post_state [Normal]) 
	      p)])
    ::bhv.b_extended
  | _ -> typing_context.Logic_typing.error loc
    "expecting a predicate after keyword 'typically'"

let () = Logic_typing.register_behavior_extension "typically" typically_typer




type index =
| I of Integer.t
| All
| L of logic_var
type simple_var =
  varinfo
type complex_var =
| CVVCont of varinfo * index
| CVCCont of complex_var * index
type var =
| Simple of simple_var
| Complex of complex_var
| Logic of logic_var
type compo_var =
| Dim of var
| Var of var
| Int of Integer.t
| Float of float
| Plus of compo_var * compo_var
| Minus of compo_var * compo_var
| Mult of compo_var * compo_var
| Div of compo_var * compo_var
type simple_domain =
| SDVarInt of simple_var * Integer.t * Integer.t
| SDVarFloat of simple_var * float * float
| SDDimInt of simple_var * Integer.t * Integer.t
type complex_domain =
| CDVarInt of complex_var * Integer.t * Integer.t
| CDVarFloat of complex_var * float * float
| CDDimInt of complex_var * Integer.t * Integer.t
type compo_rel =
  relation * compo_var * compo_var
type quantif_compo_rel =
  logic_var list * compo_rel list * compo_rel
    



let simple_domains = ref ([] : simple_domain list)
let complex_domains = ref ([] : complex_domain list)
let unquantifs = ref ([]: compo_rel list)
let quantifs = ref ([] : quantif_compo_rel list)


(* simple_domain -> unit *)
let add_simple_domain x = simple_domains := x :: !simple_domains

(* complex_domain -> unit *)
let add_complex_domain x = complex_domains := x :: !complex_domains

(* compo_rel -> unit *)
let add_unquantif x = unquantifs := x :: !unquantifs

(* quantif_compo_rel -> unit *)
let add_quantif x = quantifs := x :: !quantifs

(* index -> index -> bool *)
let same_index i j =
  match (i,j) with
  | I v, I w -> v = w
  | All, All -> true
  | _ -> false

(* simple_var -> simple_var -> bool *)
let same_simple_var v w = v.vname = w.vname

(* complex_var -> complex_var -> bool *)
let rec same_complex_var v w =
  match (v,w) with
  | CVVCont (v,i), CVVCont (w,j) -> v.vname = w.vname && same_index i j
  | CVCCont (v,i), CVCCont (w,j) -> same_complex_var v w && same_index i j
  | _ -> false

(* logic_var -> logic_var -> bool *)
let same_logic_var v w =
  v.lv_name = w.lv_name

(* var -> var -> bool *)
let same_var v w =
  match (v,w) with
  | Simple v, Simple w -> same_simple_var v w
  | Complex v, Complex w -> same_complex_var v w
  | Logic v, Logic w -> same_logic_var v w
  | _ -> false

(* compo_var -> compo_var -> bool *)
let rec same_compo_var v w =
  match (v,w) with
  | Var v, Var w -> same_var v w
  | Int i, Int j -> i = j
  | Float i, Float j -> i = j
  | Plus (v,w), Plus(a,b) -> (same_compo_var v a && same_compo_var w b)
    || (same_compo_var v w && same_compo_var w a)
  | Minus (v,w), Minus(a,b) -> same_compo_var v a && same_compo_var w b
  | _ -> false

(* complex_var -> bool *)
let rec isf_complex_var = function
  | CVVCont (v,_) -> isFloatingType v.vtype
  | CVCCont (v,_) -> isf_complex_var v

(* var -> bool *)
let isf_var = function
  | Simple v -> isFloatingType v.vtype
  | Complex v -> isf_complex_var v
  | Logic l -> isLogicFloatType l.lv_type

(* compo_var -> bool *)
let rec isf = function
  | Var v -> isf_var v
  | Dim v -> isf_var v
  | Int _ -> false
  | Float _ -> true
  | Plus (v,w) | Minus (v,w) -> (isf v) || (isf w)
  | Mult (v,_) | Div (v,_) -> isf v

(* logic_var -> string *)
let logic_var_to_string lv = String.uppercase lv.lv_name

(* index -> string *)
let index_to_string = function
  | I i -> Integer.to_string i
  | All -> "_"
  | L lv -> logic_var_to_string lv

(* simple_var -> string *)
let simple_var_to_string v = Printf.sprintf "'%s'" v.vname

(* complex_var -> string *)
let rec complex_var_to_string = function
  | CVVCont (vi, i) ->
    Printf.sprintf "cont(%s,%s)" (simple_var_to_string vi) (index_to_string i)
  | CVCCont (cv, i) ->
    Printf.sprintf "cont(%s,%s)" (complex_var_to_string cv) (index_to_string i)

(* compo_var -> string *)
let strop v = if isf v then "real(math)" else "int(math)"

(* var -> string *)
let strvar = function
  | Simple vi -> simple_var_to_string vi
  | Complex cv -> complex_var_to_string cv
  | Logic lv -> logic_var_to_string lv

(* compo_var -> string *)
let rec strcvar k = match k with
  | Var v -> strvar v
  | Dim v -> Printf.sprintf "dim(%s)" (strvar v)
  | Int i -> Integer.to_string i
  | Float f -> string_of_float f
  | Plus (v,w) ->  Printf.sprintf "+(%s, %s, %s)"(strop v)(strcvar v)(strcvar w)
  | Minus (v,w) -> Printf.sprintf "-(%s, %s, %s)"(strop v)(strcvar v)(strcvar w)
  | Mult (v,w) ->  Printf.sprintf "*(%s, %s, %s)"(strop v)(strcvar v)(strcvar w)
  | Div (v,w) ->   Printf.sprintf "/(%s, %s, %s)"(strop v)(strcvar v)(strcvar w)

(* simple_domain -> string *)
let strsd = function
  | SDVarInt (v,i,j) -> Printf.sprintf "%s, int([%s..%s])"
    (simple_var_to_string v) (Integer.to_string i) (Integer.to_string j)
  | SDVarFloat (v,i,j) -> Printf.sprintf "%s, float([(%f)..(%f)])"
    (simple_var_to_string v) i j
  | SDDimInt (v,i,j) -> Printf.sprintf "dim(%s), int([%s..%s])"
    (simple_var_to_string v) (Integer.to_string i) (Integer.to_string j)

(* complex_domain -> string *)
let strcd = function
  | CDVarInt (v,i,j) -> Printf.sprintf "%s, [], int([%s..%s])"
    (strvar (Complex v)) (Integer.to_string i) (Integer.to_string j)
  | CDVarFloat (v,i,j) -> Printf.sprintf "%s, [], float([(%f)..(%f)])"
    (strvar (Complex v)) i j
  | CDDimInt (v,i,j) -> Printf.sprintf "dim(%s), [], int([%s..%s])"
    (strvar (Complex v)) (Integer.to_string i) (Integer.to_string j)

(* relation -> string *)
let strrel = function
  | Rlt -> "inf"
  | Rgt -> "sup"
  | Rle -> "infegal"
  | Rge -> "supegal"
  | Req -> "egal"
  | Rneq -> "diff"

(* string -> string -> string *)
let virgule x y = if x = "" then y else (x ^ ", " ^ y)

(* string list -> string *)
let fold_virgule l = List.fold_left virgule "" l

(* compo_rel -> string *)
let struqrel (rel,x,y) =
  Printf.sprintf "cond(%s,%s,%s,pre)" (strrel rel) (strcvar x) (strcvar y)

(* quantif_compo_rel -> string *)
let strqrel (lvars, compo_rels, (rel,x,y)) =
  Printf.sprintf "uq_cond([%s],[%s],%s,%s,%s)"
    (fold_virgule (List.map (fun z -> String.uppercase z.lv_name) lvars))
    (fold_virgule (List.map struqrel compo_rels))
    (strrel rel) (strcvar x) (strcvar y)

(* string *)
let prolog_header =
  ":- module(test_parameters).\n"
  ^ ":- import create_input_val/3 from substitution.\n"
  ^ ":- export dom/4.\n"
  ^ ":- export create_input_vals/2.\n"
  ^ ":- export unquantif_preconds/2.\n"
  ^ ":- export quantif_preconds/2.\n"
  ^ ":- export strategy/2.\n"
  ^ ":- export precondition_of/2.\n\n"
  ^ "dom(0,0,0,0).\n"

(* unit -> int *)
let machdep() =
  match Kernel.Machdep.get() with
  | "x86_64" -> 64
  | "x86_32" | "ppc_32" -> 32
  | "x86_16" -> 16
  | _ -> 32

(* predicate named -> unit -> string *)
let pred_to_string x () =
  Pretty_utils.sfprintf "%a" Printer.pp_predicate_named x

(* term -> 'a *)
(* used for debugging *)
let error_term term =
  match term.term_node with
  | TLogic_coerce _ -> failwith "TLogic_coerce"
  | TBinOp _ -> failwith "TBinOp"
  | Trange _ -> failwith "Rrange"
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
  | Tat (_,LogicLabel(_,str)) -> failwith (Printf.sprintf "Tat(_,%s)" str)
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
  | _ -> failwith ("term: "^(Pretty_utils.sfprintf "%a" Printer.pp_term term))

(* fieldinfo -> Integer.t *)
let fieldinfo_to_int fi =
  let rec aux cpt = function
    | {forig_name=s}::_ when s = fi.forig_name -> Integer.of_int cpt
    | _::t -> aux (cpt+1) t
    | _ -> assert false
  in aux 0 fi.fcomp.cfields



(* logic_type -> bool *)
let is_integer = function Linteger | Ctype (TInt _) -> true | _ -> false

(* logic_type -> bool *)
let is_float = function Lreal | Ctype (TFloat _) -> true | _ -> false


(* term_lval -> var *)
let rec tlval_to_prolog tlval =
  match tlval with
  | (TVar lv, _) when lv.lv_origin = None -> Logic lv
  | (TVar lv, TNoOffset) -> Simple (Extlib.the lv.lv_origin)
  | (TVar lv, TField (fi, tof)) ->
    let i = fieldinfo_to_int fi in
    let rec aux cv = function
      | TNoOffset -> cv
      | TField (f, toff) -> aux (CVCCont(cv, I (fieldinfo_to_int f))) toff
      | TIndex ({term_node=TConst (Integer (ii, _))}, toff) ->
	aux (CVCCont(cv, I ii)) toff
      | _ -> assert false
    in Complex (aux (CVVCont((Extlib.the lv.lv_origin), I i)) tof)
  | (TVar lv, TIndex ({term_node=TConst (Integer (k, _))}, tof)) ->
    let rec aux cv = function
      | TNoOffset -> cv
      | TField (f, toff) -> aux (CVCCont(cv, I (fieldinfo_to_int f))) toff
      | TIndex ({term_node=TConst (Integer (ii, _))}, toff) ->
	aux (CVCCont(cv, I ii)) toff
      | _ -> assert false
    in Complex (aux (CVVCont((Extlib.the lv.lv_origin), I k)) tof)
  | (TMem {term_node=TLval tl}, TNoOffset) -> tlval_to_prolog tl
  | (TMem {term_node=TLval tl}, TField (fi, tof)) ->
    let var = tlval_to_prolog tl in
    let i = fieldinfo_to_int fi in
    let rec aux cv = function
      | TNoOffset -> cv
      | TField (f, toff) -> aux (CVCCont(cv, I (fieldinfo_to_int f))) toff
      | TIndex ({term_node=TConst (Integer (ii, _))}, toff) ->
	aux (CVCCont(cv, I ii)) toff
      | _ -> assert false
    in (match var with
    | Simple s -> Complex (aux (CVVCont(s, I i)) tof)
    | Complex c -> Complex (aux (CVCCont(c, I i)) tof)
    | Logic _ -> assert false)
  | (TMem {term_node=TLval tl},
     TIndex ({term_node=TConst (Integer (k, _))}, tof)) ->
    let var = tlval_to_prolog tl in
    let rec aux cv = function
      | TNoOffset -> cv
      | TField (f, toff) -> aux (CVCCont(cv, I (fieldinfo_to_int f))) toff
      | TIndex ({term_node=TConst (Integer (ii, _))}, toff) ->
	aux (CVCCont(cv, I ii)) toff
      | _ -> assert false
    in (match var with
    | Simple s -> Complex (aux (CVVCont(s, I k)) tof)
    | Complex c -> Complex (aux (CVCCont(c, I k)) tof)
    | Logic _ -> assert false)
  | (TMem term, TNoOffset) ->
    begin
      match term_to_compo_var term with
      | Var v | Dim v -> v
      | Int _ -> assert false
      | Float _ -> assert false
      | Plus (x,y) -> 
	begin
	  match (x,y) with 
	  | (Var(Simple s), Var(Logic l)) -> Complex(CVVCont(s,L l))
	  | (Var(Complex c), Var(Logic l)) -> Complex(CVCCont(c,L l))
	  | (Var(Simple s), Int i) -> Complex(CVVCont(s,I i))
	  | (Var(Complex c), Int i) -> Complex(CVCCont(c,I i))
	  | _ ->
	    Options.Self.feedback "%s+%s" (strcvar x) (strcvar y);
	    assert false
	end
      | Minus _ | Mult _ | Div _ -> assert false
    end
  | _ -> failwith
    ("term_lval: "^(Pretty_utils.sfprintf "%a" Printer.pp_term_lval tlval))


(* term -> compo_var *)
and term_to_compo_var term =
  match term.term_node with
  | TLogic_coerce (_,t) -> term_to_compo_var t
  | TConst (Integer (ii, _)) -> Int ii
  | TConst (LReal {r_nearest=f}) -> Float f
  | TLval tl -> Var (tlval_to_prolog tl)
  | TBinOp (op, t1, t2) when op = PlusA || op = PlusPI || op = IndexPI ->
    let v1 = term_to_compo_var t1 in
    let v2 = term_to_compo_var t2 in
    Plus (v1, v2)
  | TBinOp (op, t1, t2) when op = MinusA || op = MinusPI ->
    let v1 = term_to_compo_var t1 in
    let v2 = term_to_compo_var t2 in
    Minus (v1, v2)
  | TBinOp (Cil_types.Mult, t1, t2) ->
    let v1 = term_to_compo_var t1 in
    let v2 = term_to_compo_var t2 in
    Mult (v1, v2)
  | TBinOp (Cil_types.Div, t1, t2) ->
    let v1 = term_to_compo_var t1 in
    let v2 = term_to_compo_var t2 in
    Div (v1, v2)
  | TUnOp (Neg, term) ->
    (match (term_to_compo_var term) with
    | Int i -> Int (Integer.neg i)
    | _ -> failwith "term_to_compo_var: TUnOp")
  | Tat(t,LogicLabel(_,label)) when label = "Old" -> term_to_compo_var t
  | _ -> error_term term

(* term -> unit *)
let valid_to_prolog term =
  match term.term_node with
  | Tempty_set -> ()
  | TLval tlval ->
    let var = tlval_to_prolog tlval in
    add_unquantif (Req, (Dim var), (Int Integer.one))
  | TBinOp (PlusPI, {term_node=TLval tlval},
	    {term_node=(Trange (Some z, Some x))}) when isLogicZero z ->
    let var = tlval_to_prolog tlval in
    let b = term_to_compo_var x in
    add_unquantif (Req, (Dim var), (Plus (b, Int Integer.one)))
  | _ -> error_term term


(* relation -> term -> term -> unit *)
let rel_to_prolog rel term1 term2 =
  let var1 = term_to_compo_var term1 in
  let var2 = term_to_compo_var term2 in
  add_unquantif (rel, var1, var2)
    
(* predicate named -> unit *)
let rec requires_to_prolog pred =
  match pred.content with
  | Pand (p1, p2) -> requires_to_prolog p1; requires_to_prolog p2
  | Ptrue -> ()
  | Pvalid (_, term) | Pvalid_read (_, term) -> valid_to_prolog term
  | Pforall (_quantif, _pn) -> (*forall_to_prolog quantif pn*) ()
  | Prel (rel, pn1, pn2) -> rel_to_prolog rel pn1 pn2
  | _ ->
    Options.Self.feedback
      "Predicate ignored: %a" Printer.pp_predicate_named pred

(* typ -> var -> unit *)
let rec create_input_from_type ty v =
  let maxuint = max_unsigned_number (machdep()) in
  let maxint = max_signed_number (machdep()) in
  let minint = min_signed_number (machdep()) in
  let bounds = function
    | IBool -> Integer.zero, Integer.one
    | IChar | ISChar -> Integer.of_int (-128), Integer.of_int 127
    | IUChar -> Integer.zero, Integer.of_int 255
    | ik when isSigned ik -> minint, maxint
    | _ -> Integer.zero, maxuint
  in
  match (unrollType ty,v) with
  | TInt (ik,_), Simple s ->
    let b_min, b_max = bounds ik in
    add_simple_domain (SDVarInt(s,b_min,b_max))
  | TInt (ik,_), Complex s ->
    let b_min, b_max = bounds ik in
    add_complex_domain (CDVarInt(s,b_min,b_max))
  | TComp (ci,_,_), Simple s ->
    let i = ref 0 in
    List.iter (fun field ->
      create_input_from_type field.ftype
	(Complex (CVVCont (s, I (Integer.of_int !i))));
      i := !i + 1
    ) ci.cfields
  | TComp (ci,_,_), Complex s ->
    let i = ref 0 in
    List.iter (fun field ->
      create_input_from_type field.ftype
	(Complex (CVCCont (s,I (Integer.of_int !i))));
      i := !i + 1
    ) ci.cfields
  (* fixed-length arrays *)
  | TPtr (t,attr), Simple s->
    let a = findAttribute "arraylen" attr in
    if a <> [] then
      List.iter (function AInt ii ->
	add_simple_domain (SDDimInt (s,ii,ii));
	create_input_from_type t (Complex (CVVCont (s,All)))
      | _ -> ()
      ) a
    else
      (add_simple_domain (SDDimInt (s, Integer.zero, maxuint));
       create_input_from_type t (Complex (CVVCont (s,All))))
  | TPtr (t,attr), Complex s ->
    let a = findAttribute "arraylen" attr in
    if a <> [] then
      List.iter (function AInt ii ->
	add_complex_domain (CDDimInt (s,ii,ii));
	create_input_from_type t (Complex (CVCCont (s,All)))
      | _ -> ()
      ) a
    else
      (add_complex_domain (CDDimInt (s, Integer.zero, maxuint));
       create_input_from_type t (Complex (CVCCont (s,All))))
  | _ -> assert false

(* varinfo -> unit *)
let create_input_val var = create_input_from_type var.vtype (Simple var)

(* (simple_domain -> unit) -> unit *)
let iter_on_simple_domains f = List.iter f !simple_domains

(* (complex_domain -> unit) -> unit *)
let iter_on_complex_domains f = List.iter f !complex_domains

(* (compo_rel -> unit) -> unit *)
let iter_on_unquantifs f = List.iter f !unquantifs

(* (quantif_compo_rel -> unit) -> unit *)
let iter_on_quantifs f = List.iter f !quantifs

(* (simple_domain -> 'a) -> 'a list *)
let map_on_simple_domains f = List.map f !simple_domains

(* (complex_domain -> 'a) -> 'a list *)
let map_on_complex_domains f = List.map f !complex_domains

(* (compo_rel -> 'a) -> 'a list *)
let map_on_unquantifs f = List.map f !unquantifs

(* (quantif_compo_rel -> 'a) -> 'a list *)
let map_on_quantifs f = List.map f !quantifs





let translate() =
  let kf = fst (Globals.entry_point()) in
  let func_name = Kernel_function.get_name kf in
  let bhv = ref None in
  Annotations.iter_behaviors
    (fun _ b -> if is_default_behavior b then bhv := Some b) kf;
  let bhv = !bhv in
  match bhv with
  | None -> ()
  | Some bhv ->
    begin
      let requires = List.map Logic_const.pred_of_id_pred bhv.b_requires in
      let typically = List.filter (fun (s,_,_) -> s = "typically")
	bhv.b_extended in
      let typically = List.map (fun (_,_,pred) -> pred) typically in
      List.iter (fun l ->
	let ll = List.map Logic_const.pred_of_id_pred l in
	Prop_id.typically := true;
	List.iter requires_to_prolog ll
      ) typically;
      Options.Self.feedback "non-default behaviors ignored!";
      let formals = Kernel_function.get_formals kf in
      List.iter create_input_val formals;
      List.iter requires_to_prolog requires;
      let chan = open_out (Options.Precond_File.get()) in
      output chan prolog_header;
      
      (* DOM *)
      iter_on_complex_domains (fun x ->
	output chan (Printf.sprintf "dom('%s', %s).\n" func_name (strcd x))
      );
      let precond_name = "pathcrawler__" ^ func_name ^ "_precond" in
      output chan (Printf.sprintf "dom('%s',A,B,C) :- dom('%s',A,B,C).\n"
		     precond_name func_name);
      
      (* CREATE_INPUT_VALS *)
      output chan
	(Printf.sprintf "create_input_vals('%s', Ins):-\n" func_name);
      iter_on_simple_domains (fun s ->
	output chan (Printf.sprintf "  create_input_val(%s,Ins),\n" (strsd s))
      );
      output chan "  true.\n";
      output chan
	(Printf.sprintf
	   "create_input_vals('%s',Ins) :- create_input_vals('%s',Ins).\n"
	   precond_name func_name);
      
      (* QUANTIF_PRECONDS *)
      let qp = map_on_quantifs strqrel in
      let qp = fold_virgule qp in
      output chan
	(Printf.sprintf "quantif_preconds('%s',[%s]).\n" func_name qp);
      output chan
	(Printf.sprintf
	   "quantif_preconds('%s',A) :- quantif_preconds('%s',A).\n"
	   precond_name func_name);
      
      
      (* UNQUANTIF_PRECONDS *)
      let uqp = map_on_unquantifs struqrel in
      let uqp = fold_virgule uqp in
      output chan
	(Printf.sprintf"unquantif_preconds('%s',[%s]).\n"func_name uqp);
      output chan
	(Printf.sprintf
	   "unquantif_preconds('%s',A) :- unquantif_preconds('%s',A).\n"
	   precond_name func_name);


      output chan (Printf.sprintf "strategy('%s',[]).\n" func_name);
      output chan (Printf.sprintf "strategy('%s',A) :- strategy('%s',A).\n"
		     precond_name func_name);
      output chan (Printf.sprintf "precondition_of('%s','%s').\n"
		     func_name precond_name);
      flush chan;
      close_out chan;
      simple_domains := [];
      complex_domains := [];
      unquantifs := [];
      quantifs := []
    end

