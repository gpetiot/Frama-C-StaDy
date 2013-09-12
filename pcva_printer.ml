
open Cil
open Cil_types
open Lexing




let debug_builtins = Kernel.register_category "printer:builtins"
let print_var v =
  not (Cil.is_unused_builtin v) || Kernel.is_debug_key_enabled debug_builtins



  

exception PredUnsupported of predicate named
exception TermUnsupported of term




class pcva_printer () = object (self)
  inherit Printer.extensible_printer () as super

  val mutable current_function = None

  method private in_current_function vi =
    assert (current_function = None);
    current_function <- Some vi

  method private out_current_function =
    assert (current_function <> None);
    current_function <- None

  method private opt_funspec fmt funspec =
    if logic_printer_enabled && not (Cil.is_empty_funspec funspec) then
      Format.fprintf fmt "@[<hv 1>/*@@ %a@ */@]@\n" self#funspec funspec

  method private vdecl_complete fmt v =
    let display_ghost = v.vghost && not is_ghost in
    Format.fprintf fmt "@[<hov 0>%t%a;%t@]"
      (if display_ghost then fun fmt -> Format.fprintf fmt "/*@@ ghost@ "
       else ignore)
      self#vdecl v
      (if display_ghost then fun fmt -> Format.fprintf fmt "@ */" else ignore)

  method private term_lhost_to_lhost = function
  | TVar lv -> Var (Extlib.the lv.lv_origin)
  | TResult _ -> failwith "term_lhost_to_lhost"
  | TMem te -> Mem (self#term_to_exp te)

  method private term_offset_to_offset = function
  | TNoOffset  -> NoOffset
  | TField (fi, toff) -> Field (fi, (self#term_offset_to_offset toff))
  | TModel _ -> failwith "term_offset_to_offset"
  | TIndex(te,teo)-> Index(self#term_to_exp te,self#term_offset_to_offset teo)

  method private term_to_type t =
    match t.term_type with
    | Ctype ty -> ty
    | _ -> failwith "term_to_type"

  method private term_to_exp_node t = match t.term_node with
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
    
  method private term_to_exp t =
    new_exp ~loc:(t.term_loc) (self#term_to_exp_node t)

  (* exp -> (exp * exp) *)
  method private extract_exps exp =
    let loc = exp.eloc in
    match exp.enode with
    | Lval (Var v, NoOffset) -> evar v, zero ~loc
    | BinOp (PlusPI,x,y,_)
    | BinOp (IndexPI,x,y,_) -> x,y
    | BinOp (MinusPI,x,y,_) -> x,(new_exp ~loc (UnOp(Neg,y,intType)))
    | _ -> failwith (Pretty_utils.sfprintf "%a" Printer.pp_exp exp)


  method private predicate fmt pred =
    match pred with
    | Ptrue -> Format.fprintf fmt "1"
    | Pfalse -> Format.fprintf fmt "0"
    | Pvalid(_,term)
    | Pvalid_read(_,term) ->
      let e = self#term_to_exp term in
      let x, y = self#extract_exps e in
      Format.fprintf fmt "pathcrawler_dimentions(%a) > %a"
	self#exp x self#exp y
    | _ -> super#predicate fmt pred

  method private predicate_named fmt pred_named =
    self#predicate fmt pred_named.content

      

  method private annotated_stmt next fmt stmt =
    let kf = Kernel_function.find_englobing_kf stmt in
    let begin_loop = ref [] in
    let end_loop = ref [] in
    Annotations.iter_code_annot (fun _emitter ca ->
      let prop = Property.ip_of_code_annot_single kf stmt ca in
      let id = Prop_id.to_id prop in
      let ca = ca.annot_content in
      let behaviors =
	match ca with
	| AAssert (b,_)
	| AStmtSpec (b,_)
	| AInvariant (b,_,_) -> b
	| _ -> []
      in
      let behaviors =
	List.map (fun bname ->
	  let ret = ref [] in
	  Annotations.iter_behaviors (fun _emit beh ->
	    if beh.b_name = bname then
	      ret := beh.b_assumes
	  ) kf;
	  !ret
	) behaviors
      in
      let pc_assert_exception fmt pred msg id =
	Format.fprintf fmt
	  "@[<v 2>if(!(%a))@[<hv>pathcrawler_assert_exception(\"%s\", %i);@]@]"
	  self#predicate_named pred msg id
      in
      match ca with
      | AAssert (_,pred) ->
	if behaviors = [] then
	  pc_assert_exception fmt pred "Assert!" id
	else
	  begin
	    Format.fprintf fmt "@[<v 2>if (";
	    List.iter (fun assumes ->
	      Format.fprintf fmt "(";
	      List.iter (fun a ->
		Format.fprintf fmt "%a &&" self#predicate a.ip_content
	      ) assumes;
	      Format.fprintf fmt " 1 ) || "
	    ) behaviors;
	    Format.fprintf fmt " 0 )@]";
	    pc_assert_exception fmt pred "Assert!" id
	  end
      | AInvariant (_,true,pred) ->
	if behaviors = [] then
	  begin
	    pc_assert_exception fmt pred "Loop invariant not established!" id;
	    end_loop :=
	      (fun fmt ->
		pc_assert_exception fmt pred
		  "Loop invariant not preserved!" id)
	    :: !end_loop
	  end
	else
	  begin
	    Format.fprintf fmt "@[<v 2>if (";
	    List.iter (fun assumes ->
	      Format.fprintf fmt "(";
	      List.iter (fun a ->
		Format.fprintf fmt "%a &&" self#predicate a.ip_content
	      ) assumes;
	      Format.fprintf fmt " 1 ) || "
	    ) behaviors;
	    Format.fprintf fmt " 0 )@]";
	    pc_assert_exception fmt pred "Loop invariant not established!" id;
	    end_loop :=
	      (fun fmt ->
		Format.fprintf fmt "@[<v 2>if (";
		List.iter (fun assumes ->
		  Format.fprintf fmt "(";
		  List.iter (fun a ->
		    Format.fprintf fmt "%a &&" self#predicate a.ip_content
		  ) assumes;
		  Format.fprintf fmt " 1 ) || "
		) behaviors;
		Format.fprintf fmt " 0 )@]";
		pc_assert_exception fmt pred "Loop invariant not preserved!" id)
	    :: !end_loop
	  end
      | AVariant (term,_) ->
	Format.fprintf fmt
	  "@[<v 2>if((%a)<0)@[<hv>pathcrawler_assert_exception(\"%s\",%i);@]@]"
	  self#term term "Variant non positive!" id;
	begin_loop :=
	  (fun fmt ->
	    Format.fprintf fmt "int old_variant_%i = %a;\n" id self#term term)
	:: !begin_loop;
	end_loop :=
	  (fun fmt ->
	    Format.fprintf fmt
	      "@[<v 2>if((%a) >= old_variant_%i)@[<hv>pathcrawler_assert_exception(\"%s\",%i);@]@]"
	      self#term term id "Variant non decreasing!" id)
	:: !end_loop
      | _ -> ()
    ) stmt;

    match stmt.skind with
    | Loop(_,b,l,_,_) ->
      Format.fprintf fmt "%a@[<v 2>while (1) {"
	(fun fmt -> self#line_directive fmt) l;
      List.iter (fun s -> s fmt) !begin_loop;
      Format.fprintf fmt "%a" (fun fmt -> self#block fmt) b;
      List.iter (fun s -> s fmt) !end_loop;
      Format.fprintf fmt "} @]"
	

    | _ -> self#stmtkind next fmt stmt.skind



  method private fundecl fmt f =
    (* declaration. *)
    let was_ghost = is_ghost in
    let entering_ghost = f.svar.vghost && not was_ghost in
    Format.fprintf fmt "@[%t%a@\n@[<v 2>"
      (if entering_ghost then fun fmt -> Format.fprintf fmt "/*@@ ghost@ " 
       else ignore)
      self#vdecl f.svar;
    (* We take care of locals in blocks. *)
    (*List.iter (fprintf fmt "@\n%a;" self#vdecl) f.slocals ;*)
    (* body. *)
    if entering_ghost then is_ghost <- true;
    self#block ~braces:true fmt f.sbody;
    if entering_ghost then is_ghost <- false;
    Format.fprintf fmt "@]%t@]@."
      (if entering_ghost then fun fmt -> Format.fprintf fmt "@ */" else ignore)


  method global fmt (g:global) =
    match g with
    | GFun (fundec, l) ->
      if print_var fundec.svar
      then begin
	self#in_current_function fundec.svar;
	(* If the function has attributes then print a prototype because
	 * GCC cannot accept function attributes in a definition *)
	let oldattr = fundec.svar.vattr in
	(* Always pring the file name before function declarations *)
	(* Prototype first *)
	if oldattr <> [] then
	  (self#line_directive fmt l;
	   Format.fprintf fmt "%a;@\n"
	     self#vdecl_complete fundec.svar);
	(* Temporarily remove the function attributes *)
	fundec.svar.vattr <- [];
	(* Body now *)
	self#line_directive ~forcefile:true fmt l;
	self#fundecl fmt fundec;
	fundec.svar.vattr <- oldattr;
	Format.fprintf fmt "@\n";
	self#out_current_function
      end

    | GType (typ, l) ->
      self#line_directive ~forcefile:true fmt l;
      Format.fprintf fmt "typedef %a;@\n"
	(self#typ (Some (fun fmt -> Format.fprintf fmt "%s" typ.tname)))
	typ.ttype

    | GEnumTag (enum, l) ->
      self#line_directive fmt l;
      if verbose then 
        Format.fprintf fmt "/* Following enum is equivalent to %a */@\n" 
          (self#typ None) 
          (TInt(enum.ekind,[]));
      Format.fprintf fmt "enum@[ %a {@\n%a@]@\n}%a;@\n"
	self#varname enum.ename
	(Pretty_utils.pp_list ~sep:",@\n"
	   (fun fmt item ->
	     Format.fprintf fmt "%s = %a"
	       item.einame
	       self#exp item.eival))
	enum.eitems
	self#attributes enum.eattr

    | GEnumTagDecl (enum, l) -> (* This is a declaration of a tag *)
      self#line_directive fmt l;
      Format.fprintf fmt "enum %a;@\n" self#varname enum.ename

    | GCompTag (comp, l) -> (* This is a definition of a tag *)
      let n = comp.cname in
      let su =
	if comp.cstruct then "struct"
	else "union"
      in
      let sto_mod, rest_attr = Cil.separateStorageModifiers comp.cattr in
      self#line_directive ~forcefile:true fmt l;
      Format.fprintf fmt "@[<3>%s%a %a {@\n%a@]@\n}%a;@\n"
	su
	self#attributes sto_mod
	self#varname n
	(Pretty_utils.pp_list ~sep:"@\n" self#fieldinfo)
	comp.cfields
	self#attributes rest_attr

    | GCompTagDecl (comp, l) -> (* This is a declaration of a tag *)
      self#line_directive fmt l;
      Format.fprintf fmt "%s;@\n" (Cil.compFullName comp)

    | GVar (vi, io, l) ->
      if print_var vi then begin
	self#line_directive ~forcefile:true fmt l;
        if vi.vghost then Format.fprintf fmt "/*@@ ghost@ ";
	self#vdecl fmt vi;
	(match io.init with
	  None -> ()
	| Some i ->
	  Format.fprintf fmt " = ";
	  let islong =
	    match i with
	      CompoundInit (_, il) when List.length il >= 8 -> true
	    | _ -> false
	  in
	  if islong then begin
	    self#line_directive fmt l;
	    Format.fprintf fmt "  @[@\n"
	  end;
	  self#init fmt i;
	  if islong then Format.fprintf fmt "@]");
	Format.fprintf fmt ";%t@\n" 
          (if vi.vghost then fun fmt -> Format.fprintf fmt "@ */" else ignore)
      end
    (* print global variable 'extern' declarations, and function prototypes *)
    | GVarDecl (funspec, vi, l) ->
      if print_var vi then begin
	if Cil.isFunctionType vi.vtype then self#in_current_function vi;
	self#opt_funspec fmt funspec;
	begin
	  self#line_directive fmt l;
	  Format.fprintf fmt "%a@\n@\n" self#vdecl_complete vi
	end;
	if Cil.isFunctionType vi.vtype then self#out_current_function
      end

    | GAsm (s, l) ->
      self#line_directive fmt l;
      Format.fprintf fmt "__asm__(\"%s\");@\n" (Escape.escape_string s)

    | GPragma (Attr(_an, _args), _l) -> Format.fprintf fmt "@\n"

    | GPragma (AttrAnnot _, _) -> Format.fprintf fmt "@\n"

    | GAnnot (decl,l) ->
      self#line_directive fmt l;
      Format.fprintf fmt "/*@@@ %a@ */@\n"
	self#global_annotation decl

    | GText s  ->
      if s <> "//" then
	Format.fprintf fmt "%s@\n" s

end


include Printer_builder.Make(struct class printer = pcva_printer end)


 

