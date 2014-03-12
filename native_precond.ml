
open Cil_types




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






type pl_constant =
| PLInt of Integer.t
| PLFloat of float

type pl_term =
| PLBinOp of pl_term * binop * pl_term
| PLConst of pl_constant
| PLDim of pl_term
| PLContAll of pl_term
| PLCont of pl_term * pl_term
| PLLVar of logic_var
| PLCVar of varinfo

type pl_domain =
| PLIntDom of pl_term * Integer.t * Integer.t
| PLFloatDom of pl_term * string * string

type pl_rel = pl_term * relation * pl_term

type pl_quantif = logic_var list * pl_rel list * pl_rel

type pl_constraint =
| PLUnquantif of pl_rel
| PLQuantif of pl_quantif
| PLDomain of pl_domain






let rec is_complex_term : pl_term -> bool =
  function
  | PLBinOp (t1,_,t2) -> is_complex_term t1 || is_complex_term t2
  | PLDim t -> is_complex_term t
  | PLContAll _ -> true
  | PLCont (t1,t2) -> is_complex_term t1 || is_complex_term t2
  | PLConst _ | PLLVar _ | PLCVar _ -> false

let is_complex_domain : pl_domain -> bool =
  function PLIntDom (t,_,_) | PLFloatDom (t,_,_) -> is_complex_term t

class pl_printer = object(self)
  method pl_constant : pl_constant -> string =
    function
    | PLInt i -> Integer.to_string i
    | PLFloat f -> "(" ^ (string_of_float f) ^ "0)"
      
  method is_float : pl_term -> bool =
    function
    | PLConst (PLInt _) | PLDim _ -> false
    | PLConst (PLFloat _) -> true
    | PLContAll t' | PLBinOp (t',_,_) | PLCont (t',_) -> self#is_float t'
    | PLLVar lv -> Cil.isLogicFloatType lv.lv_type
    | PLCVar v -> Cil.isFloatingType v.vtype

  method binop : binop -> string =
    function
    | PlusA | PlusPI | IndexPI -> "+"
    | MinusA -> "-"
    | Mult -> "*"
    | Div -> "/"
    | _ -> assert false

  method pl_term : pl_term -> string =
    function
    | PLBinOp (t1, b, t2) ->
      Printf.sprintf "%s(%s(math), %s, %s)"
	(self#binop b)
	(if self#is_float t1 then "real" else "int")
	(self#pl_term t1)
	(self#pl_term t2)
    | PLConst c -> self#pl_constant c
    | PLDim t' -> Printf.sprintf "dim(%s)" (self#pl_term t')
    | PLContAll t' -> Printf.sprintf "cont(%s,_)" (self#pl_term t')
    | PLCont (t1, t2) ->
      Printf.sprintf "cont(%s,%s)" (self#pl_term t1) (self#pl_term t2)
    | PLLVar lv -> String.uppercase lv.lv_name
    | PLCVar v -> Printf.sprintf "'%s'" v.vname

  method pl_domain : bool -> pl_domain -> string =
    fun complex ->
      function
      | PLIntDom (t',a,b) -> Printf.sprintf "%s, %sint([%s..%s])"
	(self#pl_term t')
	(if complex then "[], " else "")
	(Integer.to_string a)
	(Integer.to_string b)
      | PLFloatDom (t',a,b) -> Printf.sprintf "%s, %sfloat([(%s)..(%s)])"
	(self#pl_term t') (if complex then "[], " else "") a b

  method relation : relation -> string =
    function
    | Rlt -> "inf"
    | Rgt -> "sup"
    | Rle -> "infegal"
    | Rge -> "supegal"
    | Req -> "egal"
    | Rneq -> "diff"

  method pl_rel : pl_rel -> string =
    fun (t1,r,t2) ->
      Printf.sprintf "cond(%s,%s,%s,pre)"
	(self#relation r)
	(self#pl_term t1)
	(self#pl_term t2)

  method pl_quantif : pl_quantif -> string =
    fun (lvars, compo_rels, (t1,r,t2)) ->
      Printf.sprintf "uq_cond([%s],[%s],%s,%s,%s)"
	(Utils.fold_comma (List.map(fun z -> String.uppercase z.lv_name) lvars))
	(Utils.fold_comma (List.map self#pl_rel compo_rels))
	(self#relation r)
	(self#pl_term t1)
	(self#pl_term t2)
end

let pp_pl_term = (new pl_printer)#pl_term
let pp_pl_domain = (new pl_printer)#pl_domain
let pp_pl_rel = (new pl_printer)#pl_rel
let pp_pl_quantif = (new pl_printer)#pl_quantif

let prolog_header : string =
  ":- module(test_parameters).\n"
  ^ ":- import create_input_val/3 from substitution.\n"
  ^ ":- export dom/4.\n"
  ^ ":- export create_input_vals/2.\n"
  ^ ":- export unquantif_preconds/2.\n"
  ^ ":- export quantif_preconds/2.\n"
  ^ ":- export strategy/2.\n"
  ^ ":- export precondition_of/2.\n\n"
  ^ "dom(0,0,0,0).\n"

let error_term : term -> 'a =
  fun term ->
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
    | Tat (_,LogicLabel(_,str)) -> Options.Self.abort "Tat(_,%s)" str
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
    | _ -> Options.Self.abort "term: %a" Printer.pp_term term

class to_pl = object(self)
  method logic_var : logic_var -> pl_term =
    fun lv ->
      match lv.lv_origin with
      | None -> PLLVar lv
      | Some v -> PLCVar v

  method term_offset : pl_term list -> term_offset -> pl_term list =
    fun ret offset ->
      match offset with
      | TNoOffset -> List.rev ret
      | TField (fi, tof) ->
	let i = PLConst (PLInt (Utils.fieldinfo_to_int fi)) in
	self#term_offset (i :: ret) tof
      | TModel _ ->
	Options.Self.debug ~dkey:Options.dkey_native_precond "TModel: %a"
	  Printer.pp_term_offset offset;
	assert false
      | TIndex (t, tof) ->
	let i = self#term t in
	self#term_offset (i :: ret) tof
	  
  method term_lhost : term_lhost -> pl_term =
    function
    | TVar v -> self#logic_var v
    | TResult _ -> assert false
    | TMem m -> PLCont (self#term m, PLConst (PLInt Integer.zero))

  method term_lval : term_lval -> pl_term =
    fun (tlhost, toffset) ->
      let tlhost' = self#term_lhost tlhost in
      let toffsets = self#term_offset [] toffset in
      List.fold_left (fun t tof -> PLCont (t, tof)) tlhost' toffsets

  method term : term -> pl_term =
    fun t ->
      match t.term_node with
      | TLogic_coerce (_, t') -> self#term t'
      | TConst (LEnum {eival={enode=Const (CInt64 (ii,_,_))}})
      | TConst (Integer (ii, _)) -> PLConst (PLInt ii)
      | TConst (LEnum {eival={enode=Const (CReal (f,_,_))}})
      | TConst (LReal {r_nearest=f}) -> PLConst (PLFloat f)
      | TConst (LEnum {eival={enode=Const (CChr c)}})
      | TConst (LChr c) -> PLConst (PLInt (Integer.of_int (int_of_char c)))
      | TLval tl -> self#term_lval tl
      | TBinOp(op,x,y)-> PLBinOp (self#term x, op, self#term y)
      | TUnOp (Neg, term) ->
	begin
	  match (self#term term) with
	  | PLConst (PLInt i) -> PLConst (PLInt (Integer.neg i))
	  | _ ->
	    Options.Self.debug ~dkey:Options.dkey_native_precond
	      "term_to_compo_var: TUnOp";
	    assert false
	end
      | Tat(t',LogicLabel(_,label)) when label = "Old" -> self#term t'
      | _ -> error_term t
end

let term_to_pl : term -> pl_term =
  fun t ->
    try
      (new to_pl)#term t
    with
    | _ ->
      Options.Self.debug ~dkey:Options.dkey_native_precond
	"term_to_pl: %a" Printer.pp_term t;
      assert false

let rec input_from_type :
    pl_domain list -> typ -> pl_term -> pl_domain list =
  fun domains ty t ->
    let maxuint = Cil.max_unsigned_number (Utils.machdep()) in
    let maxint = Cil.max_signed_number (Utils.machdep()) in
    let minint = Cil.min_signed_number (Utils.machdep()) in
    let ibounds = function
      | IBool -> Integer.zero, Integer.one
      | IChar | ISChar -> Integer.of_int (-128), Integer.of_int 127
      | IUChar -> Integer.zero, Integer.of_int 255
      | ik when Cil.isSigned ik -> minint, maxint
      | _ -> Integer.zero, maxuint
    in
    let fbounds = function
      | FFloat -> "+1.0e-37", "+1.0e+38"
      | FDouble -> "+1.0e-307", "+1.0e+308"
      | FLongDouble -> "+1.0e-307", "+1.0e+308"
    in
    match (Cil.unrollType ty) with
    | TEnum ({ekind=ik},_) | TInt (ik,_) ->
      let b_min, b_max = ibounds ik in
      PLIntDom (t, b_min, b_max) :: domains
    | TFloat (fk,_) ->
      let b_min, b_max = fbounds fk in
      PLFloatDom (t, b_min, b_max) :: domains
    | TComp (ci,_,_) ->
      let rec aux doms i = function
	| [] -> doms
	| f :: fields ->
	  let d = input_from_type doms f.ftype (PLCont (t, PLConst(PLInt i))) in
	  aux d (Integer.succ i) fields
      in
      aux domains Integer.zero ci.cfields
    | TPtr (ty',attr) ->
      let att = Cil.findAttribute "arraylen" attr in
      if att <> [] then
	let is_array_len = function AInt _ -> true | _ -> false in
	if List.exists is_array_len att then
	  match List.find is_array_len att with
	  | AInt ii ->
	    let d = PLIntDom (PLDim t, ii, ii) in
	    input_from_type (d :: domains) ty' (PLContAll t)
	  | _ -> assert false
	else
	  assert false
      else
	let d = PLIntDom (PLDim t, Integer.zero, maxuint) in
	input_from_type (d :: domains) ty' (PLContAll t)
    | _ ->
      Options.Self.feedback "input_from_type (%a) (%s)"
	Printer.pp_typ ty (pp_pl_term t);
      assert false

let valid_to_prolog : term -> pl_constraint list =
  fun term ->
    let maxuint = Cil.max_unsigned_number (Utils.machdep()) in
    match term.term_node with
    | TLval _ ->
      let t = term_to_pl term in
      [ PLDomain (PLIntDom (PLDim t, Integer.one, maxuint)) ]
    | TBinOp ((PlusPI|IndexPI), t, {term_node=(Trange (_, Some x))}) ->
      let t' = term_to_pl t in
      let x' = term_to_pl x in
      let one =  PLConst (PLInt(Integer.one)) in
      begin
	match x' with
	| PLConst (PLInt i) ->
	  let i' = Integer.add i Integer.one in
	  [ PLDomain (PLIntDom (PLDim t', i', maxuint)) ]
	| _ ->
	  [ PLDomain (PLIntDom (PLDim t', Integer.one, maxuint));
	    PLUnquantif (PLDim t', Req, PLBinOp (x', PlusA, one)) ]
      end
    | _ -> error_term term

let rel_to_prolog : relation -> term -> term -> pl_constraint =
  fun rel term1 term2 ->
    let var1 = term_to_pl term1 in
    let var2 = term_to_pl term2 in
    PLUnquantif (var1, rel, var2)

let rec requires_to_prolog :
    pl_constraint list -> predicate named -> pl_constraint list =
  fun constraints pred ->
    try
      match pred.content with
      | Pand (p, q) -> requires_to_prolog (requires_to_prolog constraints p) q
      | Ptrue -> constraints
      | Pvalid(_,t) | Pvalid_read(_,t) ->
	List.rev_append (List.rev (valid_to_prolog t)) constraints
      | Pforall (_quantif, _pn) -> constraints
      | Prel (rel, pn1, pn2) -> (rel_to_prolog rel pn1 pn2) :: constraints
      | _ -> assert false
    with
    | _ ->
      Options.Self.warning "%a unsupported" Printer.pp_predicate_named pred;
      constraints

let output chan str =
  Options.Self.debug ~dkey:Options.dkey_generated_pl "%s" str;
  output_string chan str

let translate () =
  let kf = fst (Globals.entry_point()) in
  let func_name = Kernel_function.get_name kf in
  let only_default _ b r = if Cil.is_default_behavior b then b :: r else r in
  match Annotations.fold_behaviors only_default kf [] with
  | [ bhv ] ->
    begin
      let subst pred  = (new Sd_subst.subst)#subst_pnamed pred [] [] [] [] in
      let requires = List.map Logic_const.pred_of_id_pred bhv.b_requires in
      let requires = List.map subst requires in
      let typically = List.filter (fun (s,_,_) -> s = "typically")
	bhv.b_extended in
      let typically = List.map (fun (_,_,pred) -> pred) typically in
      let constraints =
	List.fold_left (fun c l ->
	  let ll = List.map Logic_const.pred_of_id_pred l in
	  let ll = List.map subst ll in
	  let new_props = List.map (Property.ip_of_requires kf Kglobal bhv) l in
	  List.iter Property_status.register new_props;
	  Prop_id.typically := List.rev_append new_props !Prop_id.typically;
	  List.fold_left requires_to_prolog c ll
	) [] typically
      in
      Options.Self.feedback ~dkey:Options.dkey_native_precond
	"non-default behaviors ignored!";
      let constraints =List.fold_left requires_to_prolog constraints requires in
      let is_domain = function PLDomain _ -> true | _ -> false in
      let domains, constraints = List.partition is_domain constraints in
      let unfold = function PLDomain d -> d | _ -> assert false in
      let domains = List.map unfold domains in
      let is_quantif = function PLQuantif _ -> true |  _ -> false in
      let quantifs, unquantifs = List.partition is_quantif constraints in
      let unfold = function PLQuantif q -> q | _ -> assert false in
      let quantifs = List.map unfold quantifs in
      let unfold = function PLUnquantif q -> q | _ -> assert false in
      let unquantifs = List.map unfold unquantifs in
      let formals = Kernel_function.get_formals kf in
      let create_input d v = input_from_type d v.vtype (PLCVar v) in
      let domains = List.fold_left create_input domains formals in
      let domains_tbl = Hashtbl.create 32 in
      let is_int_domain = function PLIntDom _ -> true | _ -> false in
      let int_doms, float_doms = List.partition is_int_domain domains in
      let merge_int_doms = function
	| PLIntDom (t, i1, i2) ->
	  begin
	    try
	      let lower, upper = Hashtbl.find domains_tbl t in
	      let lower' = Integer.max lower i1 in
	      let upper' = Integer.max upper i2 in
	      Hashtbl.replace domains_tbl t (lower', upper')
	    with Not_found -> Hashtbl.add domains_tbl t (i1, i2)
	  end
	| PLFloatDom _ -> assert false
      in
      List.iter merge_int_doms int_doms;
      let add_int_dom_to_list k (v,w) doms =  PLIntDom (k,v,w) :: doms in
      let domains = Hashtbl.fold add_int_dom_to_list domains_tbl float_doms in
      let domains = List.rev domains in
      let chan = open_out (Options.Precond_File.get()) in
      output chan prolog_header;
      let complex_d, simple_d = List.partition is_complex_domain domains in
      let precond_name = "pathcrawler__" ^ func_name ^ "_precond" in
      let same_constraint_for_precond before after =
	output chan (Printf.sprintf "%s('%s',%s) :- %s('%s',%s).\n"
		       before precond_name after before func_name after)
      in

      (* DOM *)
      let pp_complex_d x =
	Printf.sprintf "dom('%s', %s).\n" func_name (pp_pl_domain true x) in
      List.iter (fun x -> output chan (pp_complex_d x)) complex_d;
      same_constraint_for_precond "dom" "A,B,C";
      
      (* CREATE_INPUT_VALS *)
      output chan (Printf.sprintf "create_input_vals('%s', Ins):-\n" func_name);
      let pp_simple_d x =
	Printf.sprintf "  create_input_val(%s,Ins),\n" (pp_pl_domain false x) in
      List.iter (fun x -> output chan (pp_simple_d x)) simple_d;
      output chan "  true.\n";
      same_constraint_for_precond "create_input_vals" "Ins";
      
      (* QUANTIF_PRECONDS *)
      let qp = List.map pp_pl_quantif quantifs in
      let qp = Utils.fold_comma qp in
      output chan(Printf.sprintf "quantif_preconds('%s',[%s]).\n" func_name qp);
      same_constraint_for_precond "quantif_preconds" "A";
     
      (* UNQUANTIF_PRECONDS *)
      let uqp = List.map pp_pl_rel unquantifs in
      let uqp = Utils.fold_comma uqp in
      output chan
	(Printf.sprintf"unquantif_preconds('%s',[%s]).\n" func_name uqp);
      same_constraint_for_precond "unquantif_preconds" "A";
      
      (* STRATEGY *)
      output chan (Printf.sprintf "strategy('%s',[]).\n" func_name);
      same_constraint_for_precond "strategy" "A";

      output chan
	(Printf.sprintf "precondition_of('%s','%s').\n" func_name precond_name);
      flush chan;
      close_out chan;
      true
    end
  | _ -> false
