
open Cil_types


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
  method pl_constant fmt = function
  | PLInt i -> self#pl_integer fmt i
  | PLFloat f -> Format.fprintf fmt "(%f0)" f
      
  method is_float = function
  | PLConst (PLInt _) | PLDim _ -> false
  | PLConst (PLFloat _) -> true
  | PLContAll t' | PLBinOp (t',_,_) | PLCont (t',_) -> self#is_float t'
  | PLLVar lv -> Cil.isLogicFloatType lv.lv_type
  | PLCVar v -> Cil.isFloatingType v.vtype

  method binop fmt = function
  | PlusA | PlusPI | IndexPI -> Format.fprintf fmt "+"
  | MinusA -> Format.fprintf fmt "-"
  | Mult -> Format.fprintf fmt "*"
  | Div -> Format.fprintf fmt "/"
  | _ -> assert false

  method pl_term fmt = function
  | PLBinOp (t1, b, t2) ->
    Format.fprintf fmt "%a(%s(math), %a, %a)"
      self#binop b
      (if self#is_float t1 then "real" else "int")
      self#pl_term t1
      self#pl_term t2
  | PLConst c -> self#pl_constant fmt c
  | PLDim t' -> Format.fprintf fmt "dim(%a)" self#pl_term t'
  | PLContAll t' -> Format.fprintf fmt "cont(%a,_)" self#pl_term t'
  | PLCont (t1, t2) ->
    Format.fprintf fmt "cont(%a,%a)" self#pl_term t1 self#pl_term t2
  | PLLVar lv -> Format.fprintf fmt "%s" (String.uppercase lv.lv_name)
  | PLCVar v -> Format.fprintf fmt "'%s'" v.vname

  method pl_integer fmt i = Integer.pretty fmt i

  method pl_domain fmt = function
  | PLIntDom (t',a,b) ->
    Format.fprintf fmt "%a, int([%a..%a])"
      self#pl_term t'
      self#pl_integer a
      self#pl_integer b
  | PLFloatDom (t',str1,str2) ->
    Format.fprintf fmt "%a, float([(%s)..(%s)])" self#pl_term t' str1 str2

  method pl_complex_domain fmt = function
  | PLIntDom (t',a,b) ->
    Format.fprintf fmt "%a, [], int([%a..%a])"
      self#pl_term t'
      self#pl_integer a
      self#pl_integer b
  | PLFloatDom (t',str1,str2) ->
    Format.fprintf fmt "%a, [], float([(%s)..(%s)])" self#pl_term t' str1 str2

  method relation fmt = function
  | Rlt -> Format.fprintf fmt "inf"
  | Rgt -> Format.fprintf fmt "sup"
  | Rle -> Format.fprintf fmt "infegal"
  | Rge -> Format.fprintf fmt "supegal"
  | Req -> Format.fprintf fmt "egal"
  | Rneq -> Format.fprintf fmt "diff"

  method pl_rel fmt (t1,r,t2) =
    Format.fprintf fmt "cond(%a,%a,%a,pre)"
      self#relation r
      self#pl_term t1
      self#pl_term t2

  method pl_quantif fmt (lvars, compo_rels, (t1,r,t2)) =
    Format.fprintf fmt "uq_cond(\n  [\n";
    let rec aux = function
      | [] -> ()
      | h :: [] -> Format.fprintf fmt "    %s\n" (String.uppercase h.lv_name)
      | h :: t -> Format.fprintf fmt "    %s,\n"(String.uppercase h.lv_name);
	aux t
    in
    aux lvars;
    Format.fprintf fmt "  ],\n  [\n";
    let rec aux = function
      | [] -> ()
      | h :: [] -> Format.fprintf fmt "    %a\n" self#pl_rel h
      | h :: t -> Format.fprintf fmt "    %a,\n" self#pl_rel h; aux t
    in
    aux compo_rels;
    Format.fprintf fmt "  ],\n  %a,%a,%a)"
      self#relation r
      self#pl_term t1
      self#pl_term t2
end


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
	let i = PLConst (PLInt (Sd_utils.fieldinfo_to_int fi)) in
	self#term_offset (i :: ret) tof
      | TModel _ ->
	Sd_options.Self.debug ~dkey:Sd_options.dkey_native_precond "TModel: %a"
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
	    Sd_options.Self.debug ~dkey:Sd_options.dkey_native_precond
	      "term_to_compo_var: TUnOp";
	    assert false
	end
      | Tat(t',LogicLabel(_,label)) when label = "Here" || label = "Old" ->
	self#term t'
      | _ -> Sd_utils.error_term t
end

let term_to_pl : term -> pl_term =
  let dkey = Sd_options.dkey_native_precond in
  fun t ->
    try (new to_pl)#term t
    with _ ->
      Sd_options.Self.debug ~dkey "term_to_pl: %a" Printer.pp_term t;
      assert false

let rec input_from_type :
    pl_domain list -> typ -> pl_term -> pl_domain list =
  fun domains ty t ->
    let maxuint = Cil.max_unsigned_number (Sd_utils.machdep()) in
    let maxint = Cil.max_signed_number (Sd_utils.machdep()) in
    let minint = Cil.min_signed_number (Sd_utils.machdep()) in
    let ibounds = function
      | IBool -> Integer.zero, Integer.one
      | IChar | ISChar -> Integer.of_int (-128), Integer.of_int 127
      | IUChar -> Integer.zero, Integer.of_int 255
      | ik when Cil.isSigned ik -> minint, maxint
      | _ -> Integer.zero, maxuint
    in
    let fbounds = function
      | FFloat -> "-3.40282347e+38", "3.40282347e+38"
      | FDouble -> "-1.7976931348623157e+308", "1.7976931348623157e+308"
      | FLongDouble -> "-1.7976931348623157e+308", "1.7976931348623157e+308"
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
      Sd_options.Self.feedback "input_from_type (%a) (%a)"
	Printer.pp_typ ty (new pl_printer)#pl_term t;
      assert false

let valid_to_prolog : term -> pl_constraint list =
  fun term ->
    let maxuint = Cil.max_unsigned_number (Sd_utils.machdep()) in
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
    | _ -> Sd_utils.error_term term

let rel_to_prolog : relation -> term -> term -> pl_constraint =
  fun rel term1 term2 ->
    let var1 = term_to_pl term1 in
    let var2 = term_to_pl term2 in
    PLUnquantif (var1, rel, var2)

let rec requires_to_prolog :
    pl_constraint list -> predicate named -> pl_constraint list =
  fun constraints pred ->
    match pred.content with
    | Pand (p, q) -> requires_to_prolog (requires_to_prolog constraints p) q
    | Ptrue -> constraints
    | Pvalid(_,t) | Pvalid_read(_,t) ->
      List.rev_append (List.rev (valid_to_prolog t)) constraints
    | Prel (rel, pn1, pn2) -> (rel_to_prolog rel pn1 pn2) :: constraints
    | Pat(p, LogicLabel(_,stringlabel)) when stringlabel = "Here" ->
      requires_to_prolog constraints p
    | _ -> assert false


let translate () =
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  let kf = fst (Globals.entry_point()) in
  let func_name = Kernel_function.get_name kf in
  let bhv = Sd_utils.default_behavior kf in
  let subst pred = (new Sd_subst.subst)#subst_pnamed pred [] [] [] [] in
  let requires_preds = bhv.b_requires in
  let typically_preds = Sd_utils.typically_preds bhv in
  let f constraints id_pred =
    let pnamed = Logic_const.pred_of_id_pred id_pred in
    let pnamed = subst pnamed in
    try
      requires_to_prolog constraints pnamed
    with
    | _ ->
      Sd_options.Self.warning "Native Precondition:@\n%a unsupported"
	Printer.pp_predicate_named pnamed;
      (* this predicate has not been translated in Prolog, we must translate it
	 in C. *)
      Sd_states.Not_Translated_Predicates.add id_pred.ip_id;
      constraints
  in
  let constraints = List.fold_left f [] typically_preds in
  let constraints = List.fold_left f constraints requires_preds in
  Sd_options.Self.feedback ~dkey:Sd_options.dkey_native_precond
    "non-default behaviors ignored!";
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
  let complex_d, simple_d = List.partition is_complex_domain domains in
  let precond_name = "pathcrawler__" ^ func_name ^ "_precond" in
  let same_constraint_for_precond before after =
    Format.fprintf fmt "%s('%s',%s) :-\n  %s('%s',%s).\n"
      before precond_name after before func_name after
  in
  let printer = new pl_printer in
  (* PRINTING *)
  Format.fprintf fmt "%s" prolog_header;
  List.iter
    (fun x ->
      Format.fprintf fmt "dom('%s', %a).\n"
	func_name printer#pl_complex_domain x)
    complex_d;
  same_constraint_for_precond "dom" "A,B,C";
  Format.fprintf fmt "create_input_vals('%s', Ins):-\n" func_name;
  List.iter
    (fun x ->
      Format.fprintf fmt "  create_input_val(%a,Ins),\n" printer#pl_domain x)
    simple_d;
  Format.fprintf fmt "  true.\n";
  same_constraint_for_precond "create_input_vals" "Ins";
  Format.fprintf fmt "quantif_preconds('%s',\n  [\n" func_name;
  let rec aux = function
    | [] -> ()
    | h :: [] -> Format.fprintf fmt "    %a\n" printer#pl_quantif h
    | h :: t -> Format.fprintf fmt "    %a,\n" printer#pl_quantif h; aux t
  in
  aux quantifs;
  Format.fprintf fmt "  ]\n).\n";
  same_constraint_for_precond "quantif_preconds" "A";
  Format.fprintf fmt "unquantif_preconds('%s',\n  [\n" func_name;
  let rec aux = function
    | [] -> ()
    | h :: [] -> Format.fprintf fmt "    %a\n" printer#pl_rel h
    | h :: t -> Format.fprintf fmt "    %a,\n" printer#pl_rel h; aux t
  in
  aux unquantifs;
  Format.fprintf fmt "  ]\n).\n";
  same_constraint_for_precond "unquantif_preconds" "A";
  Format.fprintf fmt "strategy('%s',[]).\n" func_name;
  same_constraint_for_precond "strategy" "A";
  Format.fprintf fmt "precondition_of('%s','%s').\n" func_name precond_name;
  (* END OF PRINTING *)
  let dkey = Sd_options.dkey_generated_pl in
  let out_file = open_out (Sd_options.Precond_File.get()) in
  Sd_options.Self.debug ~dkey "generated Prolog precondition:";
  let dkeys = Sd_options.Self.Debug_category.get() in
  if Datatype.String.Set.mem "generated-pl" dkeys then
    Buffer.output_buffer stdout buf;
  Buffer.output_buffer out_file buf;
  Format.pp_print_flush fmt();
  flush stdout;
  flush out_file;
  close_out out_file;
  Buffer.clear buf
