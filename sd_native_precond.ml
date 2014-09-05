
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
| PLIntDom of pl_term * Integer.t option * Integer.t option
| PLFloatDom of pl_term * string option * string option

type pl_rel = pl_term * relation * pl_term

type pl_quantif = logic_var list * pl_rel list * pl_rel

type pl_constraint =
| PLUnquantif of pl_rel
| PLQuantif of pl_quantif
| PLDomain of pl_domain






let in_dom =
  let rec aux = function
    | PLBinOp _ -> true
    | PLDim _ -> true
    | PLContAll _ -> true
    | PLCont _ -> true
    | PLConst _ | PLLVar _ | PLCVar _ -> false
  in
  function | PLIntDom (t,_,_) | PLFloatDom (t,_,_) -> aux t

let in_create_input_val =
  let rec aux = function
    | PLBinOp (t1,_,t2) -> aux t1 && aux t2
    | PLDim t -> aux t
    | PLContAll _ -> false
    | PLCont (t1,t2) -> aux t1 && aux t2
    | PLConst _ | PLLVar _ | PLCVar _ -> true
  in
  function | PLIntDom (t,_,_) | PLFloatDom (t,_,_) -> aux t

class pl_printer = object(self)
  method constant fmt = function
  | PLInt i -> self#integer fmt i
  | PLFloat f -> Format.fprintf fmt "(%f0)" f
      
  method private is_float = function
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

  method term fmt = function
  | PLBinOp (t1, b, t2) ->
    Format.fprintf fmt "%a(%s(math), %a, %a)"
      self#binop b
      (if self#is_float t1 then "real" else "int")
      self#term t1
      self#term t2
  | PLConst c -> self#constant fmt c
  | PLDim t' -> Format.fprintf fmt "dim(%a)" self#term t'
  | PLContAll t' -> Format.fprintf fmt "cont(%a,_)" self#term t'
  | PLCont (t1,t2) -> Format.fprintf fmt "cont(%a,%a)" self#term t1 self#term t2
  | PLLVar lv -> Format.fprintf fmt "%s" (String.uppercase lv.lv_name)
  | PLCVar v -> Format.fprintf fmt "'%s'" v.vname

  method integer fmt i = Integer.pretty fmt i

  method integer_opt fmt = function
  | Some i -> Format.fprintf fmt "%a" self#integer i
  | None -> Format.fprintf fmt "?"

  method domain fmt = function
  | PLIntDom (t',a,b) ->
    Format.fprintf fmt "%a, int([%a..%a])"
      self#term t' self#integer_opt a self#integer_opt b
  | PLFloatDom (t',str1,str2) ->
    Format.fprintf fmt "%a, float([(%s)..(%s)])"
      self#term t'
      (try Extlib.the str1 with _ -> "?")
      (try Extlib.the str2 with _ -> "?")

  method complex_domain fmt = function
  | PLIntDom (t',a,b) ->
    Format.fprintf fmt "%a, [], int([%a..%a])"
      self#term t' self#integer_opt a self#integer_opt b
  | PLFloatDom (t',str1,str2) ->
    Format.fprintf fmt "%a, [], float([(%s)..(%s)])"
      self#term t'
      (try Extlib.the str1 with _ -> "?")
      (try Extlib.the str2 with _ -> "?")

  method relation fmt = function
  | Rlt -> Format.fprintf fmt "inf"
  | Rgt -> Format.fprintf fmt "sup"
  | Rle -> Format.fprintf fmt "infegal"
  | Rge -> Format.fprintf fmt "supegal"
  | Req -> Format.fprintf fmt "egal"
  | Rneq -> Format.fprintf fmt "diff"

  method rel fmt (x,r,y) =
    Format.fprintf fmt "cond(%a,%a,%a,pre)"
      self#relation r self#term x self#term y

  method quantif fmt (lvars, compo_rels, (x,r,y)) =
    Format.fprintf fmt "uq_cond(\n  [\n";
    let rec aux = function
      | [] -> ()
      | h :: [] -> Format.fprintf fmt "    %s\n" (String.uppercase h.lv_name)
      | h :: t -> Format.fprintf fmt "    %s,\n" (String.uppercase h.lv_name);
	aux t
    in
    aux lvars;
    Format.fprintf fmt "  ],\n  [\n";
    let rec aux = function
      | [] -> ()
      | h :: [] -> Format.fprintf fmt "    %a\n" self#rel h
      | h :: t -> Format.fprintf fmt "    %a,\n" self#rel h; aux t
    in
    aux compo_rels;
    Format.fprintf fmt "  ],\n  %a,%a,%a)"
      self#relation r self#term x self#term y
end


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

class to_pl = object(self)
  method logic_var lv =
    match lv.lv_origin with
    | None -> PLLVar lv
    | Some v -> PLCVar v

  method term_offset ret = function
  | TNoOffset -> List.rev ret
  | TField (fi, tof) ->
    let i = PLConst (PLInt (Sd_utils.fieldinfo_to_int fi)) in
    self#term_offset (i :: ret) tof
  | TModel _ as t -> Sd_utils.error_toffset t
  | TIndex (t, tof) -> self#term_offset ((self#term t) :: ret) tof
	  
  method term_lhost = function
  | TVar v -> self#logic_var v
  | TResult _ -> assert false
  | TMem{term_node=TBinOp((PlusPI|IndexPI),x,y)} ->
    PLCont(self#term x,self#term y)
  | TMem m -> PLCont (self#term m, PLConst (PLInt Integer.zero))

  method term_lval (tlhost, toffset) =
    let tlhost' = self#term_lhost tlhost in
    let toffsets = self#term_offset [] toffset in
    List.fold_left (fun t tof -> PLCont (t, tof)) tlhost' toffsets

  method term t =
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
	| _ -> Sd_utils.error_term t
      end
    | Tat(t',LogicLabel(_,l)) when l = "Here" || l = "Old" -> self#term t'
    | _ -> Sd_utils.error_term t
end

let term_to_pl t = try (new to_pl)#term t with _ -> Sd_utils.error_term t

let rec input_from_type domains ty t =
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
  | TVoid _ -> PLIntDom (t, Some minint, Some maxint) :: domains
  | TEnum ({ekind=ik},_) | TInt (ik,_) ->
    let b_min, b_max = ibounds ik in
    PLIntDom (t, Some b_min, Some b_max) :: domains
  | TFloat (fk,_) ->
    let b_min, b_max = fbounds fk in
    PLFloatDom (t, Some b_min, Some b_max) :: domains
  | TComp (ci,_,_) ->
    let rec aux doms i = function
      | [] -> doms
      | f :: fields ->
	let d = input_from_type doms f.ftype (PLCont (t, PLConst(PLInt i))) in
	aux d (Integer.succ i) fields
    in
    aux domains Integer.zero ci.cfields
  | TPtr (ty',attr) | TArray (ty',_,_,attr) ->
    let att = Cil.findAttribute "arraylen" attr in
    if att <> [] then
      let is_array_len = function AInt _ -> true | _ -> false in
      if List.exists is_array_len att then
	match List.find is_array_len att with
	| AInt ii ->
	  let d = PLIntDom (PLDim t, Some ii, Some ii) in
	  input_from_type (d :: domains) ty' (PLContAll t)
	| _ -> assert false
      else
	assert false
    else
      let d = PLIntDom (PLDim t, Some Integer.zero, Some maxuint) in
      input_from_type (d :: domains) ty' (PLContAll t)
  | _ ->
    Sd_options.Self.abort "input_from_type (%a) (%a)"
      Printer.pp_typ ty (new pl_printer)#term t

let rec valid_to_prolog term =
  let maxuint = Cil.max_unsigned_number (Sd_utils.machdep()) in
  match term.term_node with
  | TLval _ ->
    let t = term_to_pl term in
    [ PLDomain (PLIntDom (PLDim t, Some (Integer.one), Some maxuint)) ]
  | TBinOp (((PlusPI|IndexPI|MinusPI) as op),
    	    ({term_node=TCastE((TPtr _) as ty,t)} as _operand1),
    	    ({term_node=(Trange (_, Some _))} as operand2)) ->
    valid_to_prolog
      {term with term_node=TBinOp(op, {t with term_type=Ctype ty}, operand2)}
  | TBinOp ((PlusPI|IndexPI), t, {term_node=(Trange (_, Some x))}) ->
    let t' = term_to_pl t in
    let x' = term_to_pl x in
    let one =  PLConst (PLInt(Integer.one)) in
    begin
      match x' with
      | PLConst (PLInt i) ->
	let i' = Integer.add i Integer.one in
	[ PLDomain (PLIntDom (PLDim t', Some i', Some maxuint)) ]
      | _ ->
	[ PLDomain (PLIntDom (PLDim t', Some (Integer.one), Some maxuint));
	  PLUnquantif (PLDim t', Req, PLBinOp (x', PlusA, one)) ]
    end
  | _ -> Sd_utils.error_term term

let rel_to_prolog rel term1 term2 =
  let var1 = term_to_pl term1 in
  let var2 = term_to_pl term2 in
  let rec no_var = function
    | PLBinOp (x,_,y) -> no_var x && no_var y
    | PLConst _ -> true
    | PLDim x -> no_var x
    | PLContAll x -> no_var x
    | PLCont (x,y) -> no_var x && no_var y
    | PLLVar _ -> false
    | PLCVar _ -> false
  in
  match var1 with
  | PLConst (PLInt x) ->
    begin
      match var2 with
      | PLDim _ | PLContAll _ | PLCont _ | PLCVar _ ->
	begin
	  match rel with
	  | Rlt -> PLDomain (PLIntDom (var2, (Some (Integer.succ x)), None))
	  | Rgt -> PLDomain (PLIntDom (var2, None, (Some (Integer.pred x))))
	  | Rle -> PLDomain (PLIntDom (var2, (Some x), None))
	  | Rge -> PLDomain (PLIntDom (var2, None, (Some x)))
	  | Req -> PLDomain (PLIntDom (var2, (Some x), (Some x)))
	  | Rneq -> PLUnquantif (var1, rel, var2)
	end
      | _ -> PLUnquantif (var1, rel, var2)
    end
  | PLCont (_, off) when not (no_var off) -> PLUnquantif (var1, rel, var2)
  | PLDim _ | PLContAll _ | PLCont _ | PLCVar _ ->
    begin
      match var2 with
      | PLConst (PLInt y) ->
	begin
	  match rel with
	  | Rlt -> PLDomain (PLIntDom (var1, None, (Some (Integer.pred y))))
	  | Rgt -> PLDomain (PLIntDom (var1, (Some (Integer.succ y)), None))
	  | Rle -> PLDomain (PLIntDom (var1, None, (Some y)))
	  | Rge -> PLDomain (PLIntDom (var1, (Some y), None))
	  | Req -> PLDomain (PLIntDom (var1, (Some y), (Some y)))
	  | Rneq -> PLUnquantif (var1, rel, var2)
	end
      | _ -> PLUnquantif (var1, rel, var2)
    end
  | _ -> PLUnquantif (var1, rel, var2)


let rec requires_to_prolog constraints pred =
  match pred.content with
  | Pand (p, q) -> requires_to_prolog (requires_to_prolog constraints p) q
  | Ptrue -> constraints
  | Pvalid(_,t) | Pvalid_read(_,t) ->
    List.rev_append (List.rev (valid_to_prolog t)) constraints
  | Prel (rel, pn1, pn2) -> (rel_to_prolog rel pn1 pn2) :: constraints
  | Pat(p,LogicLabel(_,l)) when l = "Here" -> requires_to_prolog constraints p
  | _ -> assert false


let translate precond_file_name =
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  let kf = fst (Globals.entry_point()) in
  let func_name = Kernel_function.get_name kf in
  let bhv = Sd_utils.default_behavior kf in
  let subst pred = (new Sd_subst.subst)#pnamed pred [] [] [] [] in
  let requires_preds = bhv.b_requires in
  let typically_preds = Sd_utils.typically_preds bhv in
  let f constraints id_pred =
    let pnamed = Logic_const.pred_of_id_pred id_pred in
    let pnamed = subst pnamed in
    try requires_to_prolog constraints pnamed
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
  let formals = Kernel_function.get_formals kf in
  let create_input d v = input_from_type d v.vtype (PLCVar v) in
  let domains = List.fold_left create_input domains formals in
  let domains = Globals.Vars.fold (fun v _ d -> create_input d v) domains in
  let domains_tbl = Hashtbl.create 32 in
  let is_int_domain = function PLIntDom _ -> true | _ -> false in
  let int_doms, float_doms = List.partition is_int_domain domains in
  let merge_int f a b =
    match (a,b) with
    | None, x -> x
    | x, None -> x
    | Some x, Some y -> Some (f x y)
  in
  let merge_int_doms = function
    | PLIntDom (t, i1, i2) ->
      begin
	try
	  let lower, upper = Hashtbl.find domains_tbl t in
	  let lower' = merge_int Integer.max lower i1 in
	  let upper' = merge_int Integer.min upper i2 in
	  Hashtbl.replace domains_tbl t (lower', upper')
	with Not_found -> Hashtbl.add domains_tbl t (i1, i2)
      end
    | PLFloatDom _ -> assert false
  in
  List.iter merge_int_doms int_doms;
  let extract_ops t =
    let rec aux f = function
      | PLCVar _ as t -> t, f
      | PLBinOp (a,PlusA,PLConst (PLInt b)) -> aux (fun x -> Integer.add x b) a
      | PLBinOp (a,MinusA,PLConst (PLInt b)) -> aux (fun x -> Integer.sub x b) a
      | PLBinOp (a,Mult,PLConst (PLInt b)) -> aux (fun x -> Integer.mul x b) a
      | _ -> assert false
    in
    aux (fun x -> x) t
  in
  let fixed_dims, unquantifs =
    let rec aux ret1 ret2 = function
      | (PLUnquantif (PLDim t1, Req, t2) as unquantif) :: t ->
	begin
	  try
	    let t', to_apply = extract_ops t2 in
	    let x, y = Hashtbl.find domains_tbl t' in
	    let x = to_apply (Extlib.the x) in
	    let y = to_apply (Extlib.the y) in
	    if not (Integer.equal x y) then assert false;
	    let x = Integer.succ x and y = Integer.succ y in
	    let dom = PLIntDom (PLDim t1, Some x, Some y) in
	    aux (dom::ret1) ret2 t
	  with _ -> aux ret1 (unquantif::ret2) t
	end
      | unquantif :: t -> aux ret1 (unquantif::ret2) t
      | [] -> ret1, ret2
    in
    aux [] [] unquantifs
  in
  let unquantifs = List.rev unquantifs in
  List.iter merge_int_doms fixed_dims;
  let add_int_dom_to_list k (v,w) doms =  PLIntDom (k,v,w) :: doms in
  let domains = Hashtbl.fold add_int_dom_to_list domains_tbl float_doms in
  let domains = List.rev domains in
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
      if in_dom x then
	Format.fprintf fmt "dom('%s', %a).\n"
	  func_name printer#complex_domain x)
    domains;
  same_constraint_for_precond "dom" "A,B,C";
  Format.fprintf fmt "create_input_vals('%s', Ins):-\n" func_name;
  List.iter
    (fun x ->
      if in_create_input_val x then
	Format.fprintf fmt "  create_input_val(%a,Ins),\n" printer#domain x)
    domains;
  Format.fprintf fmt "  true.\n";
  same_constraint_for_precond "create_input_vals" "Ins";
  Format.fprintf fmt "quantif_preconds('%s',\n  [\n" func_name;
  let rec aux = function
    | PLQuantif h::[] -> Format.fprintf fmt "    %a\n" printer#quantif h
    | PLQuantif h::t -> Format.fprintf fmt "    %a,\n" printer#quantif h; aux t
    | _ -> ()
  in
  aux quantifs;
  Format.fprintf fmt "  ]\n).\n";
  same_constraint_for_precond "quantif_preconds" "A";
  Format.fprintf fmt "unquantif_preconds('%s',\n  [\n" func_name;
  let rec aux = function
    | PLUnquantif h :: [] -> Format.fprintf fmt "    %a\n" printer#rel h
    | PLUnquantif h :: t -> Format.fprintf fmt "    %a,\n" printer#rel h; aux t
    | _ -> ()
  in
  aux unquantifs;
  Format.fprintf fmt "  ]\n).\n";
  same_constraint_for_precond "unquantif_preconds" "A";
  Format.fprintf fmt "strategy('%s',[]).\n" func_name;
  same_constraint_for_precond "strategy" "A";
  Format.fprintf fmt "precondition_of('%s','%s').\n" func_name precond_name;
  (* END OF PRINTING *)
  let dkey = Sd_options.dkey_generated_pl in
  let out_file = open_out precond_file_name in
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
