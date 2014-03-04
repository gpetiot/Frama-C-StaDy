
open Cil_types


let output chan str =
  Options.Self.debug ~dkey:Options.dkey_generated_pl "%s" str;
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
| PLFloatDom of pl_term * float * float

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
  function PLIntDom (t,_,_)| PLFloatDom (t,_,_) -> is_complex_term t







class pl_printer = object(self)
  method pl_constant : pl_constant -> string =
    function
    | PLInt i -> Integer.to_string i
    | PLFloat f -> string_of_float f
      
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
      | PLFloatDom (t',a,b) -> Printf.sprintf "%s, %sfloat([(%f)..(%f)])"
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
      | TConst (Integer (ii, _)) -> PLConst (PLInt ii)
      | TConst (LReal {r_nearest=f}) -> PLConst (PLFloat f)
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











let term_to_pl : term -> pl_term = fun t -> (new to_pl)#term t



let rec create_input_from_type :
    pl_domain list -> typ -> pl_term -> pl_domain list =
  fun domains ty t ->
    let maxuint = Cil.max_unsigned_number (Utils.machdep()) in
    let maxint = Cil.max_signed_number (Utils.machdep()) in
    let minint = Cil.min_signed_number (Utils.machdep()) in
    let bounds = function
      | IBool -> Integer.zero, Integer.one
      | IChar | ISChar -> Integer.of_int (-128), Integer.of_int 127
      | IUChar -> Integer.zero, Integer.of_int 255
      | ik when Cil.isSigned ik -> minint, maxint
      | _ -> Integer.zero, maxuint
    in
    match (Cil.unrollType ty) with
    | TEnum ({ekind=ik},_) | TInt (ik,_) ->
      let b_min, b_max = bounds ik in
      let d = PLIntDom (t, b_min, b_max) in
      d :: domains

    | TComp (ci,_,_) ->
      let rec aux doms fields i =
	match fields with
	| [] -> doms
	| f :: fields' ->
	  let doms' =
	    create_input_from_type doms f.ftype (PLCont (t, PLConst (PLInt i)))
	  in
	  aux doms' fields' (Integer.succ i)
      in
      aux domains ci.cfields Integer.zero

    | TPtr (ty',attr) ->
      let att = Cil.findAttribute "arraylen" attr in
      if att <> [] then
	let is_array_len = function AInt _ -> true | _ -> false in
	if List.exists is_array_len att then
	  match List.find is_array_len att with
	  | AInt ii ->
	    let d = PLIntDom (PLDim t, ii, ii) in
	    create_input_from_type (d :: domains) ty' (PLContAll t)
	  | _ -> assert false
	else
	  assert false
      else
	begin
	  let d = PLIntDom (PLDim t, Integer.zero, maxuint) in
	  create_input_from_type (d :: domains) ty' (PLContAll t)
	end
    
    | _ ->
      Options.Self.feedback "create_input_from_type (%a) (%s)"
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
      | Pand (p1, p2) ->
	requires_to_prolog (requires_to_prolog constraints p1) p2
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














let translate () =
  let kf = fst (Globals.entry_point()) in
  let func_name = Kernel_function.get_name kf in
  let bhv = ref None in
  Annotations.iter_behaviors
    (fun _ b -> if Cil.is_default_behavior b then bhv := Some b) kf;
  let bhv = !bhv in
  match bhv with
  | None -> false
  | Some bhv ->
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
      let create_input d v = create_input_from_type d v.vtype (PLCVar v) in
      let domains = List.fold_left create_input domains formals in


      let domains_tbl = Hashtbl.create 32 in
      let is_int_domain = function PLIntDom _ -> true | _ -> false in
      let int_doms, float_doms = List.partition is_int_domain domains in
      List.iter (function
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
      ) int_doms;

      
      let domains = Hashtbl.fold (fun k (v,w) doms ->
	PLIntDom (k,v,w) :: doms) domains_tbl float_doms in
      let domains = List.rev domains in
      


      let chan = open_out (Options.Precond_File.get()) in
      output chan prolog_header;
      let complex_d, simple_d = List.partition is_complex_domain domains in
      
      (* DOM *)
      List.iter (fun x ->
	output chan (Printf.sprintf "dom('%s', %s).\n"
		       func_name
		       (pp_pl_domain true x)
	)
      ) complex_d;

      let precond_name = "pathcrawler__" ^ func_name ^ "_precond" in
      output chan (Printf.sprintf "dom('%s',A,B,C) :- dom('%s',A,B,C).\n"
		     precond_name func_name);
      
      (* CREATE_INPUT_VALS *)
      output chan (Printf.sprintf "create_input_vals('%s', Ins):-\n" func_name);

      List.iter (fun s ->
	output chan (Printf.sprintf "  create_input_val(%s,Ins),\n"
		       (pp_pl_domain false s)
	)
      ) simple_d;

      output chan "  true.\n";
      output chan
	(Printf.sprintf
	   "create_input_vals('%s',Ins) :- create_input_vals('%s',Ins).\n"
	   precond_name func_name);
      
      (* QUANTIF_PRECONDS *)
      let qp = List.map pp_pl_quantif quantifs in
      let qp = Utils.fold_comma qp in
      output chan(Printf.sprintf "quantif_preconds('%s',[%s]).\n" func_name qp);
      output chan
	(Printf.sprintf
	   "quantif_preconds('%s',A) :- quantif_preconds('%s',A).\n"
	   precond_name func_name);
      
      
      (* UNQUANTIF_PRECONDS *)
      let uqp = List.map pp_pl_rel unquantifs in
      let uqp = Utils.fold_comma uqp in
      output chan
	(Printf.sprintf"unquantif_preconds('%s',[%s]).\n" func_name uqp);
      output chan
	(Printf.sprintf
	   "unquantif_preconds('%s',A) :- unquantif_preconds('%s',A).\n"
	   precond_name func_name);


      output chan (Printf.sprintf "strategy('%s',[]).\n" func_name);
      output chan (Printf.sprintf "strategy('%s',A) :- strategy('%s',A).\n"
		     precond_name func_name);
      output chan
	(Printf.sprintf "precondition_of('%s','%s').\n" func_name precond_name);
      flush chan;
      close_out chan;
      true
    end

