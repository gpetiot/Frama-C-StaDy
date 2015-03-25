
open Cil_types


let pp_label fmt = function
  | Insertions.BegStmt s -> Format.fprintf fmt "BegStmt %i" s
  | Insertions.EndStmt s -> Format.fprintf fmt "EndStmt %i" s
  | Insertions.BegFunc s -> Format.fprintf fmt "BegFunc %s" s
  | Insertions.EndFunc s -> Format.fprintf fmt "EndFunc %s" s
  | Insertions.BegIter s -> Format.fprintf fmt "BegIter %i" s
  | Insertions.EndIter s -> Format.fprintf fmt "EndIter %i" s

let pp_lval = Printer.pp_lval
let pp_exp = Printer.pp_exp
let pp_list =  Pretty_utils.pp_list ~sep:", "
let pp_instr = Printer.pp_instr

let rec pp_insertion ?(line_break = true) fmt ins =
  let rec aux fmt = function
    | [] -> ()
    | h :: [] -> pp_insertion ~line_break:false fmt h
    | h :: t -> pp_insertion ~line_break:true fmt h; aux fmt t
  in
  begin match ins with
  | Insertions.Instru i -> Format.fprintf fmt "@[%a@]" pp_instr i
  | Insertions.IRet e -> Format.fprintf fmt "@[return %a;@]" pp_exp e
  | Insertions.Decl v ->
     let ty = Cil.stripConstLocalType v.vtype in
     let array_to_ptr = function TArray(t,_,_,a) -> TPtr(t,a) | t -> t in
     let ty = array_to_ptr ty in
     let v' = {v with vtype = ty} in
     Format.fprintf fmt "@[%a;@]" (new Printer.extensible_printer())#vdecl v'
  | Insertions.Block b ->
     if b <> [] then Format.fprintf fmt "@[<hov 2>{@\n%a@]@\n}" aux b
  | Insertions.IIf (e,b1,b2) ->
     Format.fprintf fmt "@[<hov 2>if(%a) {@\n%a@]@\n}" pp_exp e aux b1;
     if b2 <> [] then Format.fprintf fmt "@\n@[<hov 2>else {@\n%a@]@\n}" aux b2
  | Insertions.ILoop (e,b) ->
     Format.fprintf fmt "@[<hov 2>while(%a) {@\n%a@]@\n}" pp_exp e aux b
  end;
  if line_break then Format.fprintf fmt "@\n"

let pp_insertion_lb = pp_insertion ~line_break:true


let debug_builtins = Kernel.register_category "printer:builtins"

let print_var v =
  not (Cil.is_unused_builtin v) || Kernel.is_debug_key_enabled debug_builtins


class print_insertions insertions functions cwd () = object(self)
  inherit Printer.extensible_printer () as super

  method private insertions_at fmt label =
    try
      let q = Hashtbl.find insertions label in
      Queue.iter (pp_insertion_lb fmt) q
    with _ -> ()

  method private fundecl fmt f =
    let entry_point_name=Kernel_function.get_name(fst(Globals.entry_point())) in
    let old_is_ghost = is_ghost in
    is_ghost <- true;
    (* BEGIN precond (entry-point) *)
    if f.svar.vname = entry_point_name then begin
      let precond = f.svar.vname ^ "_precond" in
      let x,y,z =
	match f.svar.vtype with TFun(_,x,y,z) -> x,y,z | _ -> assert false
      in
      Format.fprintf fmt "%a@ @[<hov 2>{@\n"
	(self#typ (Some (fun fmt -> Format.fprintf fmt "%s" precond)))
	(TFun(Cil.intType,x,y,z));
      self#insertions_at fmt (Insertions.BegFunc precond);
      Format.fprintf fmt "@[return 1;@]";
      Format.fprintf fmt "@]@\n}@\n@\n"
    end;
    (* END precond (entry-point) *)
    Format.fprintf fmt "@[%t%a@\n@[<v 2>" ignore self#vdecl f.svar;
    (* body. *)
    Format.fprintf fmt "@[<hov 2>{@\n";
    self#insertions_at fmt (Insertions.BegFunc f.svar.vname);
    self#block ~braces:true fmt f.sbody;
    Format.fprintf fmt "@.}";
    Format.fprintf fmt "@]%t@]@." ignore;
    is_ghost <- old_is_ghost
  (* end of fundecl *)

  method! private annotated_stmt next fmt stmt =
    Format.pp_open_hvbox fmt 2;
    self#stmt_labels fmt stmt;
    Format.pp_open_hvbox fmt 0;
    let kf = Kernel_function.find_englobing_kf stmt in
    let insert_something =
      (try not (Queue.is_empty
		  (Hashtbl.find insertions (Insertions.BegStmt stmt.sid)))
       with _ -> false)
      || (try not (Queue.is_empty
		     (Hashtbl.find insertions (Insertions.EndStmt stmt.sid)))
	with _ -> false)
    in
    if insert_something then Format.fprintf fmt "@[<hov 2>{@\n";
    self#insertions_at fmt (Insertions.BegStmt stmt.sid);
    begin
      match stmt.skind with
      | Loop(_,b,l,_,_) ->
	 Format.fprintf fmt "%a@[<v 2>while (1) {@\n"
			(fun fmt -> self#line_directive fmt) l;
	 let new_b = {b with bstmts = [List.hd b.bstmts]} in
	 let braces = false in
	 Format.fprintf fmt "%a" (fun fmt -> self#block ~braces fmt) new_b;
	 self#insertions_at fmt (Insertions.BegIter stmt.sid);
	 let new_b = {b with bstmts = List.tl b.bstmts} in
	 let new_b = {new_b with blocals = []} in
	 Format.fprintf fmt "%a" (fun fmt -> self#block ~braces fmt) new_b;
	 self#insertions_at fmt (Insertions.EndIter stmt.sid);
	 Format.fprintf fmt "}@\n @]"
      | Instr(Call(_,{enode=Lval(Var vi,NoOffset)},_,_))
	  when (cwd <> None && (Extlib.the cwd).sid = stmt.sid)
	       || List.mem vi.vname (Options.Simulate_Functions.get()) -> ()
      | Return _ ->
	let f = Kernel_function.get_name kf in
	self#insertions_at fmt (Insertions.EndFunc f);
	self#stmtkind next fmt stmt.skind
      | _ -> self#stmtkind next fmt stmt.skind
    end;
    self#insertions_at fmt (Insertions.EndStmt stmt.sid);
    if insert_something then Format.fprintf fmt "@]@\n}";
    Format.pp_close_box fmt ();
    Format.pp_close_box fmt ()
  (* end of annotated_stmt *)

  method private func_header fmt f =
    let ty = f.Insertions.func_var.vtype in
    let vname = f.Insertions.func_var.vname in
    Format.fprintf fmt "@[%a;@\n@]"
      (self#typ (Some (fun fmt -> Format.fprintf fmt "%s" vname))) ty

  method private func fmt f =
    let ty = f.Insertions.func_var.vtype in
    let vname = f.Insertions.func_var.vname in
    Format.fprintf fmt "@[<v 2>%a {@\n"
      (self#typ (Some (fun fmt -> Format.fprintf fmt "%s" vname))) ty;
    let rec aux = function
      | [] -> ()
      | [h] -> Format.fprintf fmt "%a" (pp_insertion ~line_break:false) h
      | h::t -> Format.fprintf fmt "%a" (pp_insertion ~line_break:true) h; aux t
    in
    aux f.Insertions.func_stmts;
    Format.fprintf fmt "@]@\n}@\n"

  method! file fmt f =
    Format.fprintf fmt "@[/* Generated by Frama-C */@\n";
    self#headers fmt;
    Cil.iterGlobals f (fun g -> self#global fmt g);
    List.iter (fun x -> self#func fmt x) functions;
    Format.fprintf fmt "@]@."

  val mutable gmp = false
  val mutable gmpz_get_ui = false
  val mutable gmpz_get_si = false
  val mutable gmpz_cmp = false
  val mutable gmpz_cmp_ui = false
  val mutable gmpz_cmp_si = false
  val mutable gmpz_clear = false
  val mutable gmpz_init = false
  val mutable gmpz_init_set = false
  val mutable gmpz_init_set_ui = false
  val mutable gmpz_init_set_si = false
  val mutable gmpz_init_set_str = false
  val mutable gmpz_set = false
  val mutable gmpz_abs = false
  val mutable gmpz_add = false
  val mutable gmpz_add_ui = false
  val mutable gmpz_sub = false
  val mutable gmpz_sub_ui = false
  val mutable gmpz_ui_sub = false
  val mutable gmpz_mul = false
  val mutable gmpz_mul_si = false
  val mutable gmpz_mul_ui = false
  val mutable gmpz_tdiv_q = false
  val mutable gmpz_tdiv_q_ui = false
  val mutable gmpz_tdiv_r = false
  val mutable gmpz_tdiv_r_ui = false
  val mutable gmpz_mul_2exp = false
  val mutable gmpz_fdiv_q_2exp = false
  val mutable pc_assert_exc = false
  val mutable pc_dim = false
  val mutable pc_to_fc = false
  val mutable pc_assume = false
  val mutable malloc = false
  val mutable free = false
  val mutable nondet = false

  method private instru = function
  | Call (_,{enode=Lval(Var v,_)},_,_) ->
    if v.vname = "malloc" then malloc <- true
    else if v.vname = "free" then free <- true
    else if v.vname = "pathcrawler_dimension" then pc_dim <- true
    else if v.vname = "pathcrawler_assert_exception" then pc_assert_exc <- true
    else if v.vname = "pathcrawler_assume_exception" then pc_assume <- true
    else if v.vname = "pathcrawler_to_framac" then pc_to_fc <- true
    else if v.vname = "__gmpz_clear" then (gmpz_clear <- true; gmp <- true)
    else if v.vname = "__gmpz_init" then gmpz_init <- true
    else if v.vname = "__gmpz_init_set" then gmpz_init_set <- true
    else if v.vname = "__gmpz_init_set_ui" then gmpz_init_set_ui <- true
    else if v.vname = "__gmpz_init_set_si" then gmpz_init_set_si <- true
    else if v.vname = "__gmpz_init_set_str" then gmpz_init_set_str <- true
    else if v.vname = "__gmpz_set" then gmpz_set <- true
    else if v.vname = "__gmpz_abs" then gmpz_abs <- true
    else if v.vname = "__gmpz_add" then gmpz_add <- true
    else if v.vname = "__gmpz_add_ui" then gmpz_add_ui <- true
    else if v.vname = "__gmpz_sub" then gmpz_sub <- true
    else if v.vname = "__gmpz_sub_ui" then gmpz_sub_ui <- true
    else if v.vname = "__gmpz_ui_sub" then gmpz_ui_sub <- true
    else if v.vname = "__gmpz_mul" then gmpz_mul <- true
    else if v.vname = "__gmpz_mul_ui" then gmpz_mul_ui <- true
    else if v.vname = "__gmpz_mul_si" then gmpz_mul_si <- true
    else if v.vname = "__gmpz_tdiv_q" then gmpz_tdiv_q <- true
    else if v.vname = "__gmpz_tdiv_q_ui" then gmpz_tdiv_q_ui <- true
    else if v.vname = "__gmpz_tdiv_r" then gmpz_tdiv_r <- true
    else if v.vname = "__gmpz_tdiv_r_ui" then gmpz_tdiv_r_ui <- true
    else if v.vname = "__gmpz_get_ui" then gmpz_get_ui <- true
    else if v.vname = "__gmpz_get_si" then gmpz_get_si <- true
    else if v.vname = "__gmpz_cmp" then gmpz_cmp <- true
    else if v.vname = "__gmpz_cmp_ui" then gmpz_cmp_ui <- true
    else if v.vname = "__gmpz_cmp_si" then gmpz_cmp_si <- true
    else if v.vname = "__gmpz_mul_2exp" then gmpz_mul_2exp <- true
    else if v.vname = "__gmpz_fdiv_q_2exp" then gmpz_fdiv_q_2exp <- true
    else if (String.sub v.vname 0 7) = "nondet_" then
      begin
	nondet <- true; pc_dim <- true; pc_assume <- true
      end
  | _ -> ()

  method private insertion = function
  | Insertions.Instru i -> self#instru i
  | Insertions.IRet _ -> ()
  | Insertions.Decl _ -> ()
  | Insertions.Block i -> List.iter self#insertion i
  | Insertions.IIf(_,i1,i2) ->
     List.iter self#insertion i1; List.iter self#insertion i2
  | Insertions.ILoop(_,i) -> List.iter self#insertion i

  method private headers fmt =
    Hashtbl.iter (fun _ q -> Queue.iter self#insertion q) insertions;
    let on_func f = List.iter self#insertion f.Insertions.func_stmts in
    List.iter on_func functions;
    let nondet_file = Options.Self.Share.file ~error:true "nondet.c" in
    let bitcnt = "unsigned long long" (*"mp_bitcnt_t"*) in
    let headers = [
      gmp, "struct __anonstruct___mpz_struct_1 {\
	    int _mp_alloc ;\
	    int _mp_size ;\
	    unsigned long *_mp_d ;\
	    };\
	    typedef struct __anonstruct___mpz_struct_1 __mpz_struct;\
	    typedef __mpz_struct mpz_t[1];";
      gmpz_get_ui, "extern unsigned long int __gmpz_get_ui(mpz_t);";
      gmpz_get_si, "extern signed long int __gmpz_get_si(mpz_t);";
      gmpz_cmp_ui, "extern int __gmpz_cmp_ui(mpz_t, unsigned long int);";
      gmpz_cmp_si, "extern int __gmpz_cmp_si(mpz_t, signed long int);";
      gmpz_cmp, "extern int __gmpz_cmp(mpz_t, mpz_t);";
      gmpz_clear, "extern void __gmpz_clear(mpz_t);";
      gmpz_init, "extern void __gmpz_init(mpz_t);";
      gmpz_init_set, "extern void __gmpz_init_set(mpz_t, mpz_t);";
      gmpz_init_set_ui,
      "extern void __gmpz_init_set_ui(mpz_t, unsigned long int);";
      gmpz_init_set_si,
      "extern void __gmpz_init_set_si(mpz_t, signed long int);";
      gmpz_init_set_str,
      "extern void __gmpz_init_set_str(mpz_t, const char*, int);";
      gmpz_set, "extern void __gmpz_set(mpz_t, mpz_t);";
      gmpz_abs, "extern void __gmpz_abs(mpz_t, mpz_t);";
      gmpz_add, "extern void __gmpz_add(mpz_t, const mpz_t, const mpz_t);";
      gmpz_add_ui,
      "extern void __gmpz_add_ui(mpz_t, const mpz_t, unsigned long int);";
      gmpz_sub, "extern void __gmpz_sub(mpz_t, const mpz_t, const mpz_t);";
      gmpz_sub_ui,
      "extern void __gmpz_sub_ui(mpz_t, const mpz_t, unsigned long int);";
      gmpz_ui_sub,
      "extern void __gmpz_ui_sub(mpz_t, unsigned long int, const mpz_t);";
      gmpz_mul, "extern void __gmpz_mul(mpz_t, const mpz_t, const mpz_t);";
      gmpz_mul_si, "extern void __gmpz_mul_si(mpz_t, const mpz_t, long int);";
      gmpz_mul_ui,
      "extern void __gmpz_mul_ui(mpz_t, const mpz_t, unsigned long int);";
      gmpz_tdiv_q,
      "extern void __gmpz_tdiv_q(mpz_t, const mpz_t, const mpz_t);";
      gmpz_tdiv_q_ui,
      "extern void __gmpz_tdiv_q_ui(mpz_t, const mpz_t, unsigned long int);";
      gmpz_tdiv_r,
      "extern void __gmpz_tdiv_r(mpz_t, const mpz_t, const mpz_t);";
      gmpz_tdiv_r_ui,
      "extern void __gmpz_tdiv_r_ui(mpz_t, const mpz_t, unsigned long int);";
      gmpz_mul_2exp,
      "extern void __gmpz_mul_2exp(mpz_t rop, const mpz_t op1,"^bitcnt^" op2);";
      gmpz_fdiv_q_2exp,
      "extern void __gmpz_fdiv_q_2exp(mpz_t q, const mpz_t n,"^bitcnt^" b);";
      pc_assert_exc, "extern int pathcrawler_assert_exception(char*,int);";
      pc_dim, "extern int pathcrawler_dimension(void*);";
      pc_to_fc, "extern void pathcrawler_to_framac(char*);";
      pc_assume, "extern int pathcrawler_assume_exception(char*,int);";
      malloc, "extern void* malloc(unsigned long);";
      free, "extern void free(void*);";
      nondet, ("#include \""^nondet_file^"\"");
    ] in
    let do_header (print, s) = if print then Format.fprintf fmt "%s@\n" s in
    List.iter do_header headers

  val mutable first_global = true

  method! global fmt g = match g with
    | GFun (fundec, l) ->
       if print_var fundec.svar then
	 begin
	   if first_global then
	     begin
	       List.iter (fun x -> self#func_header fmt x) functions;
	       first_global <- false
	     end;
	   let oldattr = fundec.svar.vattr in
	   fundec.svar.vattr <- [];
	   self#line_directive ~forcefile:true fmt l;
	   self#fundecl fmt fundec;
	   fundec.svar.vattr <- oldattr;
	   Format.fprintf fmt "@\n"
	 end
    | GVarDecl (vi, _)
    | GFunDecl (_, vi, _) -> if print_var vi then super#global fmt g
    | GVar (vi,_,_) ->
      let old_vghost = vi.vghost in
      vi.vghost <- false;
      super#global fmt g;
      vi.vghost <- old_vghost
    | _ -> super#global fmt g
end
