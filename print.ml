
open Cil_types


class print_insertions insertions functions swd = object(self)
  inherit Printer.extensible_printer () as super

  method private insertions_at fmt label =
    try
      let vars, stmts = Hashtbl.find insertions label in
      Queue.iter (Insertion.pretty_var fmt) vars;
      Queue.iter (Format.fprintf fmt "@[%a@]@\n" Printer.pp_stmt) stmts
    with _ -> ()

  method private fundecl fmt f =
    let entry_point_name=Kernel_function.get_name(fst(Globals.entry_point())) in
    let old_is_ghost = is_ghost in
    is_ghost <- true;
    (* BEGIN precond (entry-point) *)
    if f.svar.vname = entry_point_name then
      begin
	let precond = f.svar.vname ^ "_precond" in
	let x,y,z =
	  match f.svar.vtype with TFun(_,x,y,z) -> x,y,z | _ -> assert false
	in
	let print fmt = Format.fprintf fmt "%s" precond in
	Format.fprintf fmt "%a@ @[<hov 2>{@\n" (self#typ (Some print))
		       (TFun(Cil.intType,x,y,z));
	self#insertions_at fmt (Symbolic_label.beg_func precond);
	Format.fprintf fmt "@[return 1;@]";
	Format.fprintf fmt "@]@\n}@\n@\n"
      end;
    (* END precond (entry-point) *)
    Format.fprintf fmt "@[%t%a@\n@[<v 2>" ignore self#vdecl f.svar;
    (* body. *)
    Format.fprintf fmt "@[<hov 2>{@\n";
    self#insertions_at fmt (Symbolic_label.beg_func f.svar.vname);
    self#block ~braces:true fmt f.sbody;
    Format.fprintf fmt "@.}";
    Format.fprintf fmt "@]%t@]@." ignore;
    is_ghost <- old_is_ghost

  method! private annotated_stmt next fmt stmt =
    Format.pp_open_hvbox fmt 2;
    self#stmt_labels fmt stmt;
    Format.pp_open_hvbox fmt 0;
    let kf = Kernel_function.find_englobing_kf stmt in
    let insert_something l =
      let v, s = Hashtbl.find insertions l in
      not (Queue.is_empty v && Queue.is_empty s) in
    let insert_something =
      (try insert_something (Symbolic_label.beg_stmt stmt.sid) with _ -> false)
      || (try insert_something(Symbolic_label.end_stmt stmt.sid) with _-> false)
    in
    if insert_something then Format.fprintf fmt "@[<hov 2>{@\n";
    self#insertions_at fmt (Symbolic_label.beg_stmt stmt.sid);
    begin
      match stmt.skind with
      | Loop (_,b,l,_,_) when List.mem stmt.sid swd ->
	 let line_directive fmt = self#line_directive fmt in
	 let loop_cond = Utils.loop_condition stmt in
	 Format.fprintf fmt "%a@[<v 2>if (%a) {@\n" line_directive l
	   super#exp loop_cond;
	 let braces = false in
	 self#insertions_at fmt (Symbolic_label.beg_iter stmt.sid);
	 let new_b = {b with bstmts = List.tl b.bstmts} in
	 let new_b = {new_b with blocals = []} in
	 Format.fprintf fmt "%a" (fun fmt -> self#block ~braces fmt) new_b;
	 self#insertions_at fmt (Symbolic_label.end_iter stmt.sid);
	 Format.fprintf fmt "}@\n @]"
      | Loop(_,b,l,_,_) ->
	 let line_directive fmt = self#line_directive fmt in
	 Format.fprintf fmt "%a@[<v 2>while (1) {@\n" line_directive l;
	 let new_b = {b with bstmts = [List.hd b.bstmts]} in
	 let braces = false in
	 Format.fprintf fmt "%a" (fun fmt -> self#block ~braces fmt) new_b;
	 self#insertions_at fmt (Symbolic_label.beg_iter stmt.sid);
	 let new_b = {b with bstmts = List.tl b.bstmts} in
	 let new_b = {new_b with blocals = []} in
	 Format.fprintf fmt "%a" (fun fmt -> self#block ~braces fmt) new_b;
	 self#insertions_at fmt (Symbolic_label.end_iter stmt.sid);
	 Format.fprintf fmt "}@\n @]"
      | Instr(Call(_,{enode=Lval(Var vi,NoOffset)},_,_))
	   when List.mem stmt.sid swd
		|| List.mem vi.vname (Options.Simulate_Functions.get()) -> ()
      | Return _ ->
	 let f = Kernel_function.get_name kf in
	 self#insertions_at fmt (Symbolic_label.end_func f);
	 self#stmtkind next fmt stmt.skind
      | _ -> self#stmtkind next fmt stmt.skind
    end;
    self#insertions_at fmt (Symbolic_label.end_stmt stmt.sid);
    if insert_something then Format.fprintf fmt "@]@\n}";
    Format.pp_close_box fmt ();
    Format.pp_close_box fmt ()

  method! file fmt f =
    self#headers fmt;
    Cil.iterGlobals f (fun g -> self#global fmt g);
    List.iter (fun x -> Function.pretty fmt x) functions

  method private headers fmt =
    let is_nondet b i = b || Insertion.is_stmt_nondet i in
    let on_hash _ (_,q) b = b || Queue.fold is_nondet b q in
    let on_func b f = b || Function.is_nondet f in
    let nondet = Hashtbl.fold on_hash insertions false in
    let nondet = List.fold_left on_func nondet functions in
    let externals_file = Options.Share.file ~error:true "externals.h" in
    let nondet_file = Options.Share.file ~error:true "nondet.c" in
    Format.fprintf fmt "#include \"%s\"@\n" externals_file;
    if nondet then Format.fprintf fmt "#include \"%s\"@\n" nondet_file;
    Format.fprintf fmt "@\n"

  val mutable first_global = true

  method! global fmt g = match g with
    | GFun (fundec, l) ->
       if first_global then
	 begin
	   List.iter (fun x -> Function.pretty_header fmt x) functions;
	   first_global <- false
	 end;
       let oldattr = fundec.svar.vattr in
       fundec.svar.vattr <- [];
       self#line_directive ~forcefile:true fmt l;
       self#fundecl fmt fundec;
       fundec.svar.vattr <- oldattr;
       Format.fprintf fmt "@\n"
    | GVar (vi,_,_) ->
       let old_vghost = vi.vghost in
       vi.vghost <- false;
       super#global fmt g;
       vi.vghost <- old_vghost
    | _ -> super#global fmt g
end
