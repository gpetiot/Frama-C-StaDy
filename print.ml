
open Cil_types


let rec pp_insertion ?(line_break = true) fmt ins =
  let rec aux fmt = function
    | [] -> ()
    | h :: [] -> pp_insertion ~line_break:false fmt h
    | h :: t -> pp_insertion ~line_break:true fmt h; aux fmt t
  in
  begin match ins with
  | Insertions.Instru i -> Format.fprintf fmt "@[%a@]" Printer.pp_instr i
  | Insertions.IRet e -> Format.fprintf fmt "@[return %a;@]" Printer.pp_exp e
  | Insertions.Decl v ->
     let ty = Cil.stripConstLocalType v.vtype in
     let array_to_ptr = function TArray(t,_,_,a) -> TPtr(t,a) | t -> t in
     let ty = array_to_ptr ty in
     let v' = {v with vtype = ty} in
     Format.fprintf fmt "@[%a;@]" (new Printer.extensible_printer())#vdecl v'
  | Insertions.Block b ->
     if b <> [] then Format.fprintf fmt "@[<hov 2>{@\n%a@]@\n}" aux b
  | Insertions.IIf (e,b1,b2) ->
     Format.fprintf fmt "@[<hov 2>if(%a) {@\n%a@]@\n}" Printer.pp_exp e aux b1;
     if b2 <> [] then Format.fprintf fmt "@\n@[<hov 2>else {@\n%a@]@\n}" aux b2
  | Insertions.ILoop (e,b) ->
     Format.fprintf fmt "@[<hov 2>while(%a) {@\n%a@]@\n}" Printer.pp_exp e aux b
  end;
  if line_break then Format.fprintf fmt "@\n"

let pp_insertion_lb = pp_insertion ~line_break:true


class print_insertions insertions functions cwd () = object(self)
  inherit Printer.extensible_printer () as super

  method private insertions_at fmt label =
    try Queue.iter (pp_insertion_lb fmt) (Hashtbl.find insertions label)
    with _ -> ()

  val mutable in_vdecl = 0

  method! vdecl fmt v =
    in_vdecl <- in_vdecl+1; super#vdecl fmt v; in_vdecl <- in_vdecl-1

  (* "unname" all types, except in a variable declaration *)
  method! typ ?fundecl fmtopt fmt t =
    super#typ ?fundecl fmtopt fmt (if in_vdecl > 0 then t else (Utils.unname t))

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
    let insert_something l = not (Queue.is_empty (Hashtbl.find insertions l)) in
    let insert_something =
      (try insert_something (Symbolic_label.beg_stmt stmt.sid) with _ -> false)
      || (try insert_something(Symbolic_label.end_stmt stmt.sid) with _-> false)
    in
    if insert_something then Format.fprintf fmt "@[<hov 2>{@\n";
    self#insertions_at fmt (Symbolic_label.beg_stmt stmt.sid);
    begin
      match stmt.skind with
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
	   when List.mem stmt.sid cwd
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

  method private func_header fmt f =
    let ty = f.Insertions.func_var.vtype in
    let vname = f.Insertions.func_var.vname in
    let print fmt = Format.fprintf fmt "%s" vname in
    Format.fprintf fmt "@[%a;@\n@]" (self#typ (Some print)) ty

  method private func fmt f =
    let ty = f.Insertions.func_var.vtype in
    let vname = f.Insertions.func_var.vname in
    let print fmt = Format.fprintf fmt "%s" vname in
    Format.fprintf fmt "@[<v 2>%a {@\n" (self#typ (Some print)) ty;
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

  val mutable nondet = false

  method private instru = function
    | Call (_,{enode=Lval(Var v,_)},_,_) ->
       begin
	 try if (String.sub v.vname 0 7) = "nondet_" then nondet <- true
	 with _ -> ()
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
    let externals_file = Options.Self.Share.file ~error:true "externals.h" in
    let nondet_file = Options.Self.Share.file ~error:true "nondet.c" in
    let headers = [ nondet, ("#include \"" ^ nondet_file ^ "\"") ] in
    Format.fprintf fmt "#include \"%s\"@\n" externals_file;
    let do_header (print, s) = if print then Format.fprintf fmt "%s@\n" s in
    List.iter do_header headers

  val mutable first_global = true

  method! global fmt g = match g with
    | GFun (fundec, l) ->
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
    | GVar (vi,_,_) ->
       let old_vghost = vi.vghost in
       vi.vghost <- false;
       super#global fmt g;
       vi.vghost <- old_vghost
    | _ -> super#global fmt g
end
