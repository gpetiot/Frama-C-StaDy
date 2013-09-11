
open Cil
open Cil_types
open Lexing


(* Project.t -> string -> (Project.t -> Visitor.frama_c_visitor) -> bool ->
   Project.t

   Apply a copy visitor to a project, name it and check it.
*)
let apply_visitor prj name vis ~check =
  let new_prj =
    Project.on prj (fun () ->
      File.create_project_from_visitor name vis
    ) () in
  Project.on new_prj (fun () ->
    Cfg.clearFileCFG ~clear_id:false (Ast.get());
    Cfg.computeFileCFG (Ast.get());
    if check then
      let msg = Printf.sprintf "check_%s" name in
      Visitor.visitFramacFile (new File.check_file msg) (Ast.get())
  ) ();
  new_prj




 let id_to_prop_tbl = Datatype.Int.Hashtbl.create 32
 let prop_to_id_tbl = Property.Hashtbl.create 32

 

exception PredUnsupported of predicate named
exception TermUnsupported of term

 

class to_string = object(self)
  inherit Visitor.frama_c_inplace
      
  method term_lhost_to_lhost = function
    | TVar lv -> Var (Extlib.the lv.lv_origin)
    | TResult _ -> failwith "term_lhost_to_lhost"
    | TMem te -> Mem (self#term_to_exp te)

  method term_offset_to_offset = function
    | TNoOffset  -> NoOffset
    | TField (fi, toff) -> Field (fi, (self#term_offset_to_offset toff))
    | TModel _ -> failwith "term_offset_to_offset"
    | TIndex(te,teo)-> Index(self#term_to_exp te,self#term_offset_to_offset teo)

  method term_to_type t =
    match t.term_type with
      | Ctype ty -> ty
      | _ -> failwith "term_to_type"

  method term_to_exp_node t = match t.term_node with
    | TConst (Integer (bigint, so)) -> Const (CInt64 (bigint, IInt, so))
    | TConst (LStr str) -> Const (CStr str)
    | TConst (LWStr il) -> Const (CWStr il)
    | TConst (LChr c) -> Const (CChr c)
    | TConst (LReal {r_nearest=f}) -> Const (CReal (f, FFloat, None))
    | TConst (LEnum e) -> Const (CEnum e)
    | TLval (tl, tof) ->
      let lhost = self#term_lhost_to_lhost tl in
      let offset = self#term_offset_to_offset tof in
      Lval (lhost, offset)
    | TSizeOf ty -> SizeOf ty
    | TSizeOfE te -> SizeOfE (self#term_to_exp te)
    | TSizeOfStr str -> SizeOfStr str
    | TAlignOf ty -> AlignOf ty
    | TAlignOfE te -> AlignOfE (self#term_to_exp te)
    | TUnOp (unop, te) -> UnOp (unop, (self#term_to_exp te),
				(self#term_to_type te))
    | TBinOp (binop, t1, t2) ->
      BinOp (binop, (self#term_to_exp t1), (self#term_to_exp t2),
	     (self#term_to_type t1))
    | TCastE (ty, te) -> CastE (ty, (self#term_to_exp te))
    | TAddrOf (tl, tof) ->
      let lhost = self#term_lhost_to_lhost tl in
      let offset = self#term_offset_to_offset tof in
      AddrOf (lhost, offset)
    | TStartOf (tl, tof) ->
      let lhost = self#term_lhost_to_lhost tl in
      let offset = self#term_offset_to_offset tof in
      StartOf (lhost, offset)
    | TLogic_coerce (_, t) -> self#term_to_exp_node t
    | _ -> raise (TermUnsupported t)
			    
  method term_to_exp t =
    new_exp ~loc:(t.term_loc) (self#term_to_exp_node t)

  method rel_to_binop = function
    | Rlt -> Lt
    | Rgt -> Gt
    | Rle -> Le
    | Rge -> Ge
    | Req -> Eq
    | Rneq -> Ne

  (* exp -> (exp * exp) *)
  method extract_exps exp =
    let loc = exp.eloc in
    match exp.enode with
      | Lval (Var v, NoOffset) -> evar v, zero ~loc
      | BinOp (PlusPI,x,y,_)
      | BinOp (IndexPI,x,y,_) -> x,y
      | BinOp (MinusPI,x,y,_) -> x,(new_exp ~loc (UnOp(Neg,y,intType)))
      | _ -> failwith (Pretty_utils.sfprintf "%a" Printer.pp_exp exp)


  method predicate_to_string pred =
   match pred with
   | Pvalid(_,term)
   | Pvalid_read(_,term) ->
     let e = self#term_to_exp term in
     let x, y = self#extract_exps e in
     Pretty_utils.sfprintf "pathcrawler_dimentions(%a) > %a"
       Printer.pp_exp x Printer.pp_exp y
   | _ -> Pretty_utils.sfprintf "%a" Printer.pp_predicate pred

  method predicate_named_to_string pred_named =
    self#predicate_to_string pred_named.content


  method code_annotation_to_string ca id =
    match ca.annot_content with
    | AAssert (_,pred) ->
      Printf.sprintf
	" \n if (! (%s)) { pathcrawler_assert_exception(\"Error!\", %i); } \n"
      (self#predicate_named_to_string pred) id
    | _ ->
      Options.Self.feedback "%a unsupported" Printer.pp_code_annotation ca;
      ""
	

  method stmt_to_string stmt =
    let kf = Kernel_function.find_englobing_kf stmt in
    let stmt_str =
      match stmt.skind with
      | _ -> assert false
    in
    let result =
      Annotations.fold_code_annot (fun _ ca str ->
	let prop = Property.ip_of_code_annot_single kf stmt ca in
	let id = Property.Hashtbl.find prop_to_id_tbl prop in
	let bhv_option = Property.get_behavior prop in
	match bhv_option with
	| Some bhv ->
	  let assumes = bhv.b_assumes in
	  let assumes = List.map (fun pred -> pred.ip_content) assumes in
	  let assumes = List.map self#predicate_to_string assumes in
	  let assumes = List.fold_left
	    (fun x y -> Printf.sprintf "%s && %s" x y) "1" assumes in
	  let ca_str = self#code_annotation_to_string ca id in
	  Printf.sprintf "\n if (%s) { \n %s \n }\n %s \n" assumes ca_str str
	| None ->
	  let ca_str = self#code_annotation_to_string ca id in
	  Printf.sprintf "\n %s \n %s \n" ca_str str
      ) stmt stmt_str in
    result

  method block_to_string body =
    let s = List.map self#stmt_to_string body.bstmts in
    List.fold_left (fun x y -> x ^" "^ y) "" s

  method fundec_to_string fundec =
    Printf.sprintf "void f () { %s }" (self#block_to_string fundec.sbody)

  method global_to_string global =
    match global with
    | GFun(fundec,_) -> self#fundec_to_string fundec
    | _ -> Pretty_utils.sfprintf "%a" Printer.pp_global global

  method file_to_string file =
    let s = List.map self#global_to_string file.globals in
    List.fold_left (fun x y -> x ^" "^y) "" s
end
 


class translate_asserts_visitor prj =
object
  inherit Visitor.frama_c_copy prj
  
(*  
   method vstmt_aux stmt =
     let f s =
       let kf = Kernel_function.find_englobing_kf s in
       let stmts =
	 Annotations.fold_code_annot (fun _ ca stmts ->
	   let prop = Property.ip_of_code_annot_single kf s ca in
	   let id = Property.Hashtbl.find prop_to_id_tbl prop in
	   let bhv_option = Property.get_behavior prop in
	   match bhv_option with
	   | Some bhv ->
	     let assumes = bhv.b_assumes in
	     let assumes = List.map (fun pred -> pred.ip_content) assumes in
	     let _assumes = List.fold_left (fun p1 _p2 -> p1) Ptrue assumes in
	     Options.Self.feedback "Not implemented: asserts on behavior";
	     stmts
	   | None ->
	     begin
	       match ca.annot_content with
	       | AAssert (_,pred) ->
		 Options.Self.feedback "pred: %a"
		   Printer.pp_predicate pred.content;
		 Options.Self.feedback "stmt: %a"
		   Printer.pp_stmt s;
		 stmts
	       | _ -> stmts
	     end
	 ) s [s] in
       mkStmtCfgBlock stmts
     in
     ChangeDoChildrenPost(stmt, f)
*)
end





class translate_preconditions_visitor prj =
object
  inherit Visitor.frama_c_copy prj
    
   method vstmt_aux stmt =
     ChangeDoChildrenPost(stmt, (fun s -> s))
end



class translate_postconditions_visitor prj =
object
  inherit Visitor.frama_c_copy prj
    
   method vstmt_aux stmt =
     ChangeDoChildrenPost(stmt, (fun s -> s))
end




let run() =
  if Options.Enabled.get() then
    begin

      Kernel.Unicode.set false;

      (* Map locs to properties *)
     
      let property_id = ref 0 in
      Property_status.iter (fun property ->
	let pos1,_ = Property.location property in
	let fc_builtin = "__fc_builtin_for_normalization.i" in
	if (Filename.basename pos1.pos_fname) <> fc_builtin then
	  begin
	    Datatype.Int.Hashtbl.add id_to_prop_tbl !property_id property;
	    Property.Hashtbl.add prop_to_id_tbl property !property_id;
	    property_id := !property_id + 1
	  end
      );

      Datatype.Int.Hashtbl.iter (fun prop_id prop ->
	Options.Self.feedback "loc: %a (id: %i)" 
	  Printer.pp_location (Property.location prop) prop_id
      ) id_to_prop_tbl;

	  
      let translate_asserts =
	apply_visitor
	  (Project.current())
	  "translate_asserts"
	  (new translate_asserts_visitor)
	  ~check:true
      in

      let translate_preconditions =
	apply_visitor
	  translate_asserts
	  "translate_preconditions"
	  (new translate_preconditions_visitor)
	  ~check:true
      in

      let translate_postconditions =
	apply_visitor
	  translate_preconditions
	  "translate_postconditions"
	  (new translate_postconditions_visitor)
	  ~check:true
      in

      Project.remove ~project:translate_asserts ();
      Project.remove ~project:translate_preconditions ();
      Project.copy ~selection:(Plugin.get_selection()) translate_postconditions;

      (* do something *)

      (*Visitor.visitFramacFile (new to_string :> Visitor.frama_c_inplace)
	(Ast.get());*)
      let x = new to_string in
      Options.Self.feedback "%s" (x#file_to_string (Ast.get()));

      Project.remove ~project:translate_postconditions ()

    end






  
  
let run =
  let deps = [Ast.self; Options.Enabled.self] in
  let f, _self = State_builder.apply_once "pcva" deps run in
  f
    
let () = Db.Main.extend run
  
