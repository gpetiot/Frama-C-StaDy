
open Sd_insertions
open Cil_types


let pp_label fmt = function
  | BegStmt s -> Format.fprintf fmt "BegStmt %i" s
  | EndStmt s -> Format.fprintf fmt "EndStmt %i" s
  | BegFunc s -> Format.fprintf fmt "BegFunc %s" s
  | EndFunc s -> Format.fprintf fmt "EndFunc %s" s
  | BegIter s -> Format.fprintf fmt "BegIter %i" s
  | EndIter s -> Format.fprintf fmt "EndIter %i" s

let pp_fresh_gmp fmt = function
  | Fresh_gmp_var id -> Format.fprintf fmt "__stady_gmp_%i" id
  | My_gmp_var name -> Format.fprintf fmt "%s" name

let pp_decl_gmp fmt = function
  | Declared_gmp_var v -> pp_fresh_gmp fmt v

let pp_init_gmp fmt = function
  | Initialized_gmp_var v -> pp_decl_gmp fmt v

let pp_gexpr fmt = pp_init_gmp fmt

let rec pp_cexpr fmt = function
  | Fresh_ctype_var (id, _ty) -> Format.fprintf fmt "__stady_term_%i" id
  | My_ctype_var (_, name) -> Format.fprintf fmt "%s" name
  | Zero -> Format.fprintf fmt "0"
  | One -> Format.fprintf fmt "1"
  | Cst s -> Format.fprintf fmt "%s" s
  | Gmp_get_ui g -> Format.fprintf fmt "__gmpz_get_ui(%a)" pp_gexpr g
  | Gmp_get_si g -> Format.fprintf fmt "__gmpz_get_si(%a)" pp_gexpr g
  | Unop (op, e) -> Format.fprintf fmt "%a(%a)" Printer.pp_unop op pp_cexpr e
  | Binop (op,x,y) ->
    Format.fprintf fmt "(%a %a %a)" pp_cexpr x Printer.pp_binop op pp_cexpr y
  | Pc_dim e -> Format.fprintf fmt "pathcrawler_dimension(%a)" pp_cexpr e
  | Malloc e -> Format.fprintf fmt "malloc(%a)" pp_cexpr e
  | Cast (t, e) -> Format.fprintf fmt "(%a)%a" Printer.pp_typ t pp_cexpr e
  | Sizeof t -> Format.fprintf fmt "sizeof(%a)" Printer.pp_typ t
  | Deref e -> Format.fprintf fmt "*%a" pp_cexpr e
  | Sd_insertions.Index (e, i) ->
    Format.fprintf fmt "%a[%a]" pp_cexpr e pp_cexpr i
  | Sd_insertions.Field (e, s) -> Format.fprintf fmt "%a.%s" pp_cexpr e s
  | Of_pred p -> Format.fprintf fmt "%a" pp_pexpr p

and pp_pexpr fmt = function
  | Fresh_pred_var id -> Format.fprintf fmt "__stady_pred_%i" id
  | True -> Format.fprintf fmt "1"
  | False -> Format.fprintf fmt "0"
  | Cmp (rel, e1, e2) ->
    Format.fprintf fmt "%a %a %a"pp_cexpr e1 Printer.pp_relation rel pp_cexpr e2
  | Gmp_cmp (op, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp(%a, %a) %a 0"
      pp_gexpr g1 pp_gexpr g2 Printer.pp_binop op
  | Gmp_cmp_ui (op, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp_ui(%a, %a) %a 0"
      pp_gexpr g1 pp_cexpr g2 Printer.pp_binop op
  | Gmp_cmp_si (op, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp_si(%a, %a) %a 0"
      pp_gexpr g1 pp_cexpr g2 Printer.pp_binop op
  | Gmp_cmpr (rel, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp(%a, %a) %a 0"
      pp_gexpr g1 pp_gexpr g2 Printer.pp_relation rel
  | Gmp_cmpr_ui (rel, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp_ui(%a, %a) %a 0"
      pp_gexpr g1 pp_cexpr g2 Printer.pp_relation rel
  | Gmp_cmpr_si (rel, g1, g2) ->
    Format.fprintf fmt "__gmpz_cmp_si(%a, %a) %a 0"
      pp_gexpr g1 pp_cexpr g2 Printer.pp_relation rel
  | Lnot p -> Format.fprintf fmt "!(%a)" pp_pexpr p
  | Land (p, p') -> Format.fprintf fmt "(%a && %a)" pp_pexpr p pp_pexpr p'
  | Lor (p, p') -> Format.fprintf fmt "(%a || %a)" pp_pexpr p pp_pexpr p'

let pp_garith fmt = function
  | PlusA -> Format.fprintf fmt "add"
  | MinusA -> Format.fprintf fmt "sub"
  | Mult -> Format.fprintf fmt "mul"
  | Div -> Format.fprintf fmt "tdiv_q"
  | Mod -> Format.fprintf fmt "tdiv_r"
  | _ -> assert false (* not used by the translation *)

let pp_instruction fmt = function
  | Affect (x,y) -> Format.fprintf fmt "%a = %a" pp_cexpr x pp_cexpr y
  | Affect_pred (x,y) -> Format.fprintf fmt "%a = %a" pp_pexpr x pp_pexpr y
  | Free e -> Format.fprintf fmt "free(%a)" pp_cexpr e
  | Pc_to_framac s -> Format.fprintf fmt "pathcrawler_to_framac(\"%s\")" s
  | Pc_exn(s,i)->Format.fprintf fmt"pathcrawler_assert_exception(\"%s\",%i)" s i
  | Ret e -> Format.fprintf fmt "return %a" pp_cexpr e
  | Gmp_clear g -> Format.fprintf fmt "__gmpz_clear(%a)" pp_gexpr g
  | Gmp_init g -> Format.fprintf fmt "__gmpz_init(%a)" pp_decl_gmp g
  | Gmp_init_set (g,g') ->
    Format.fprintf fmt "__gmpz_init_set(%a, %a)" pp_decl_gmp g pp_gexpr g'
  | Gmp_init_set_ui (g,c) ->
    Format.fprintf fmt "__gmpz_init_set_ui(%a, %a)" pp_decl_gmp g pp_cexpr c
  | Gmp_init_set_si (g,c) ->
    Format.fprintf fmt "__gmpz_init_set_si(%a, %a)" pp_decl_gmp g pp_cexpr c
  | Gmp_init_set_str (g,s) ->
    Format.fprintf fmt "__gmpz_init_set_str(%a, \"%s\", 10)" pp_decl_gmp g s
  | Gmp_set(g,h)-> Format.fprintf fmt "__gmpz_set(%a, %a)" pp_gexpr g pp_gexpr h
  | Gmp_abs(g,h)-> Format.fprintf fmt "__gmpz_abs(%a, %a)" pp_gexpr g pp_gexpr h
  | Gmp_ui_sub (r,a,b) ->
    Format.fprintf fmt "__gmpz_ui_sub(%a, %a, %a)"
      pp_gexpr r pp_cexpr a pp_gexpr b
  | Gmp_binop (op,r,a,b) ->
    Format.fprintf fmt "__gmpz_%a(%a, %a, %a)"
      pp_garith op pp_gexpr r pp_gexpr a pp_gexpr b
  | Gmp_binop_ui (op,r,a,b) ->
    Format.fprintf fmt "__gmpz_%a_ui(%a, %a, %a)"
      pp_garith op pp_gexpr r pp_gexpr a pp_cexpr b
  | Gmp_binop_si (op,r,a,b) ->
    Format.fprintf fmt "__gmpz_%a_si(%a, %a, %a)"
      pp_garith op pp_gexpr r pp_gexpr a pp_cexpr b

let rec pp_insertion ?(line_break = true) fmt ins =
  let rec aux fmt = function
    | [] -> ()
    | h :: [] -> pp_insertion ~line_break:false fmt h
    | h :: t -> pp_insertion ~line_break:true fmt h; aux fmt t
  in
  begin
    match ins with
    | Instru i -> Format.fprintf fmt "@[%a;@]" pp_instruction i
    | Decl_gmp_var v -> Format.fprintf fmt "@[mpz_t %a;@]" pp_fresh_gmp v
    | Decl_ctype_var ((Fresh_ctype_var (_id, ty)) as v) ->
      Format.fprintf fmt "@[%a %a;@]" Printer.pp_typ ty pp_cexpr v
    | Decl_ctype_var (My_ctype_var (ty, name)) ->
      Format.fprintf fmt "@[%a %s;@]" Printer.pp_typ ty name
    | Decl_ctype_var _ -> assert false
    | Decl_pred_var p -> Format.fprintf fmt "@[int %a;@]" pp_pexpr p
    | Sd_insertions.If (cond,b1,b2) ->
      Format.fprintf fmt "@[<hov 2>if(%a) {@\n%a@]@\n}" pp_pexpr cond aux b1;
      if b2 <> [] then
	Format.fprintf fmt "@\n@[<hov 2>else {@\n%a@]@\n}" aux b2
    | For(None, Some e, None, b) ->
      Format.fprintf fmt "@[<hov 2>while(%a) {@\n%a@]@\n}" pp_pexpr e aux b
    | For(Some i1, Some e, Some i2, b) ->
      Format.fprintf fmt "@[<hov 2>for(%a; %a; %a) {@\n%a@]@\n}"
	pp_instruction i1 pp_pexpr e pp_instruction i2 aux b
    | For _ -> assert false (* not used by the translation *)
    | Sd_insertions.Block b ->
      if b <> [] then
	Format.fprintf fmt "@[<hov 2>{@\n%a@]@\n}" aux b
  end;
  if line_break then Format.fprintf fmt "@\n"

let pp_insertion_lb = pp_insertion ~line_break:true
let pp_insertion_nlb = pp_insertion ~line_break:false

class print_insertions insertions ~print_label () = object(self)
  inherit Printer.extensible_printer () as super

  val mutable current_function = None

  method private insertions_at fmt label =
    try
      let q = Hashtbl.find insertions label in
      Queue.iter
	(fun s ->
	  if print_label then Format.fprintf fmt "/* %a */ " pp_label label;
	  Format.fprintf fmt "%a" pp_insertion_lb s) q
    with _ -> ()

  method private fundecl fmt f =
    let was_ghost = is_ghost in
    let entry_point_name=Kernel_function.get_name(fst(Globals.entry_point())) in
    let entering_ghost = f.svar.vghost && not was_ghost in
    (* BEGIN precond (entry-point) *)
    if f.svar.vname = entry_point_name then
      begin
	let precond = f.svar.vname ^ "_precond" in
	let x,y,z =
	  match f.svar.vtype with TFun(_,x,y,z) -> x,y,z | _ -> assert false
	in
	Format.fprintf fmt "%a@ @[<hov 2>{@\n"
	  (self#typ (Some (fun fmt -> Format.fprintf fmt "%s" precond)))
	  (TFun(Cil.intType,x,y,z));
	Format.fprintf fmt "%a" self#insertions_at (BegFunc precond);
	Format.fprintf fmt "@[return 1;@]";
	Format.fprintf fmt "@]@\n}@\n@\n"
      end;
    (* END precond (entry-point) *)
    Format.fprintf fmt "@[%t%a@\n@[<v 2>"
      (if entering_ghost then fun fmt -> Format.fprintf fmt "/*@@ ghost@ " 
       else ignore)
      self#vdecl f.svar;
    (* body. *)
    if entering_ghost then is_ghost <- true;
    Format.fprintf fmt "@[<hov 2>{@\n";
    Format.fprintf fmt "%a" self#insertions_at (BegFunc f.svar.vname);
    self#block ~braces:true fmt f.sbody;
    (* EndFunc not necessary here ? *)
    Format.fprintf fmt "@.}";
    if entering_ghost then is_ghost <- false;
    Format.fprintf fmt "@]%t@]@."
      (if entering_ghost then fun fmt -> Format.fprintf fmt "@ */" else ignore)
  (* end of fundecl *)

  method! private annotated_stmt next fmt stmt =
    Format.pp_open_hvbox fmt 2;
    self#stmt_labels fmt stmt;
    Format.pp_open_hvbox fmt 0;
    let kf = Kernel_function.find_englobing_kf stmt in
    let insert_something =
      (try not (Queue.is_empty (Hashtbl.find insertions (BegStmt stmt.sid)))
       with _ -> false)
      || (try not (Queue.is_empty (Hashtbl.find insertions (EndStmt stmt.sid)))
	with _ -> false)
    in
    if insert_something then Format.fprintf fmt "@[<hov 2>{@\n";
    Format.fprintf fmt "%a" self#insertions_at (BegStmt stmt.sid);
    begin
      match stmt.skind with
      | Loop(_,b,l,_,_) ->
	Format.fprintf fmt "%a@[<v 2>while (1) {@\n"
	  (fun fmt -> self#line_directive fmt) l;
	Format.fprintf fmt "%a" self#insertions_at (BegIter stmt.sid);
	Format.fprintf fmt "%a" (fun fmt -> self#block fmt) b;
	Format.fprintf fmt "%a" self#insertions_at (EndIter stmt.sid);
	Format.fprintf fmt "}@\n @]"
      | Return _ ->
	let f = Kernel_function.get_name kf in
	Format.fprintf fmt "%a" self#insertions_at (EndFunc f);
	self#stmtkind next fmt stmt.skind
      | _ -> self#stmtkind next fmt stmt.skind
    end;
    Format.fprintf fmt "%a" self#insertions_at (EndStmt stmt.sid);
    if insert_something then Format.fprintf fmt "@]@\n}";
    Format.pp_close_box fmt ();
    Format.pp_close_box fmt ()
  (* end of annotated_stmt *)

  method! file fmt f =
    Format.fprintf fmt "@[/* Generated by Frama-C */@\n" ;
    Format.fprintf fmt "#include <gmp.h>@\n";
    Format.fprintf fmt "extern int pathcrawler_assert_exception(char*,int);@\n";
    Format.fprintf fmt "extern int pathcrawler_dimension(void*);@\n";
    Format.fprintf fmt "extern void pathcrawler_to_framac(char*);@\n";
    Format.fprintf fmt "extern void* malloc(unsigned);@\n";
    Format.fprintf fmt "extern void free(void*);@\n";
    Cil.iterGlobals f (fun g -> self#global fmt g);
    Format.fprintf fmt "@]@."

  (* unmodified *)
  method private vdecl_complete fmt v =
    let display_ghost = v.vghost && not is_ghost in
    Format.fprintf fmt "@[<hov 0>%t%a;%t@]"
      (if display_ghost then fun fmt -> Format.fprintf fmt "/*@@ ghost@ "
       else ignore)
      self#vdecl v
      (if display_ghost then fun fmt -> Format.fprintf fmt "@ */" else ignore)
  
  (* unmodified *)
  method private in_current_function vi =
    assert (current_function = None);
    current_function <- Some vi

  (* unmodified *)
  method private out_current_function =
    assert (current_function <> None);
    current_function <- None

  method! global fmt g =
    match g with
    | GFun (fundec, l) ->
      if print_var fundec.svar then
  	begin
  	  self#in_current_function fundec.svar;
  	  (* If the function has attributes then print a prototype because
  	   * GCC cannot accept function attributes in a definition *)
  	  let oldattr = fundec.svar.vattr in
  	  (* Always pring the file name before function declarations *)
  	  (* Prototype first *)
  	  if oldattr <> [] then
  	    (self#line_directive fmt l;
  	     Format.fprintf fmt "%a;@\n" self#vdecl_complete fundec.svar);
  	  (* Temporarily remove the function attributes *)
  	  fundec.svar.vattr <- [];
  	  (* Body now *)
  	  self#line_directive ~forcefile:true fmt l;
  	  self#fundecl fmt fundec;
  	  fundec.svar.vattr <- oldattr;
  	  Format.fprintf fmt "@\n";
  	  self#out_current_function
  	end
    | GVarDecl (_, vi, _) -> if print_var vi then super#global fmt g
    | _ -> super#global fmt g
  (* end of global *)
end
