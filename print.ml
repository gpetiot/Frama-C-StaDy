open Cil_types

class print_insertions insertions functions swd =
  object (self)
    inherit Printer.extensible_printer () as super

    method private insertions_at fmt label =
      try
        let vars, stmts, cleans = Hashtbl.find insertions label in
        Queue.iter (Utils.pretty_var fmt) vars ;
        Queue.iter (Format.fprintf fmt "@[%a@]@\n" Printer.pp_stmt) stmts ;
        Queue.iter (Format.fprintf fmt "@[%a@]@\n" Printer.pp_stmt) cleans
      with _ -> ()

    method private generated_fundecl fmt f =
      let print fmt = Format.fprintf fmt "%s" f.svar.vname in
      Format.fprintf fmt "@[<v 2>%a {@\n"
        ((new Printer.extensible_printer ())#typ (Some print))
        f.svar.vtype ;
      List.iter (Utils.pretty_var fmt) f.slocals ;
      List.iter (Format.fprintf fmt "@[%a@]@\n" Printer.pp_stmt) f.sbody.bstmts ;
      Format.fprintf fmt "@]@\n}@\n"

    method private fundecl fmt f =
      let old_is_ghost = is_ghost in
      is_ghost <- true ;
      Format.fprintf fmt "@[%t%a@\n@[<v 2>" ignore self#vdecl f.svar ;
      Format.fprintf fmt "@[<hov 2>{@\n" ;
      self#insertions_at fmt (Symbolic_label.beg_func f.svar.vname) ;
      self#block fmt f.sbody ;
      Format.fprintf fmt "@.}" ;
      Format.fprintf fmt "@]%t@]@." ignore ;
      is_ghost <- old_is_ghost

    method! private annotated_stmt next fmt stmt =
      Format.pp_open_hvbox fmt 2 ;
      self#stmt_labels fmt stmt ;
      Format.pp_open_hvbox fmt 0 ;
      let kf = Kernel_function.find_englobing_kf stmt in
      let insert_something l =
        let v, s, c = Hashtbl.find insertions l in
        not (Queue.is_empty v && Queue.is_empty s && Queue.is_empty c)
      in
      let insert_something_before =
        try insert_something (Symbolic_label.beg_stmt stmt.sid) with _ -> false
      in
      let insert_something_after =
        try insert_something (Symbolic_label.end_stmt stmt.sid) with _ -> false
      in
      if insert_something_before then Format.fprintf fmt "@[<hov 2>{@\n" ;
      self#insertions_at fmt (Symbolic_label.beg_stmt stmt.sid) ;
      if insert_something_before then Format.fprintf fmt "@]@\n}@\n" ;
      ( match stmt.skind with
      | Loop (_, b, l, _, _) when List.mem stmt.sid swd ->
          let line_directive fmt = self#line_directive fmt in
          let loop_cond = Utils.loop_condition stmt in
          Format.fprintf fmt "%a@[<v 2>if (%a) {@\n" line_directive l super#exp
            loop_cond ;
          self#insertions_at fmt (Symbolic_label.beg_iter stmt.sid) ;
          let new_b = {b with bstmts= List.tl b.bstmts} in
          let new_b = {new_b with blocals= []} in
          Format.fprintf fmt "%a" (fun fmt -> self#block fmt) new_b ;
          self#insertions_at fmt (Symbolic_label.end_iter stmt.sid) ;
          Format.fprintf fmt "@]@\n}@\n"
      | Loop (_, b, l, _, _) ->
          let line_directive fmt = self#line_directive fmt in
          Format.fprintf fmt "%a@[<v 2>while (1) {@\n" line_directive l ;
          let new_b = {b with bstmts= [List.hd b.bstmts]} in
          Format.fprintf fmt "%a" (fun fmt -> self#block fmt) new_b ;
          self#insertions_at fmt (Symbolic_label.beg_iter stmt.sid) ;
          let new_b = {b with bstmts= List.tl b.bstmts} in
          let new_b = {new_b with blocals= []} in
          Format.fprintf fmt "%a" (fun fmt -> self#block fmt) new_b ;
          self#insertions_at fmt (Symbolic_label.end_iter stmt.sid) ;
          Format.fprintf fmt "@]@\n}@\n"
      | If (e, b1, b2, l) ->
          if b1.bstmts = [] then (
            if b2.bstmts = [] then ()
            else
              let line_directive fmt = self#line_directive fmt in
              Format.fprintf fmt "%a@[<v 2>if (! (%a)) {@\n" line_directive l
                self#exp e ;
              Format.fprintf fmt "%a" (fun fmt -> self#block fmt) b2 ;
              Format.fprintf fmt "@]@\n}@\n" )
          else if b2.bstmts = [] then (
            let line_directive fmt = self#line_directive fmt in
            Format.fprintf fmt "%a@[<v 2>if (%a) {@\n" line_directive l
              self#exp e ;
            Format.fprintf fmt "%a" (fun fmt -> self#block fmt) b1 ;
            Format.fprintf fmt "@]@\n}@\n" )
          else
            let line_directive fmt = self#line_directive fmt in
            Format.fprintf fmt "%a@[<v 2>if (%a) {@\n" line_directive l
              self#exp e ;
            Format.fprintf fmt "%a" (fun fmt -> self#block fmt) b1 ;
            Format.fprintf fmt "@]@\n}@\n" ;
            Format.fprintf fmt "%a@[<v 2>else {@\n" line_directive l ;
            Format.fprintf fmt "%a" (fun fmt -> self#block fmt) b2 ;
            Format.fprintf fmt "@]@\n}@\n"
      | Instr (Call (_, {enode= Lval (Var vi, NoOffset)}, _, _))
       |Instr (Local_init (_, ConsInit (vi, _, _), _))
        when List.mem stmt.sid swd
             || List.mem vi.vname (Options.Simulate_Functions.get ()) ->
          ()
      | Return _ ->
          let f = Kernel_function.get_name kf in
          self#insertions_at fmt (Symbolic_label.end_func f) ;
          self#stmtkind stmt.sattr next fmt stmt.skind
      | _ -> self#stmtkind stmt.sattr next fmt stmt.skind ) ;
      if insert_something_after then Format.fprintf fmt "@[<hov 2>{@\n" ;
      self#insertions_at fmt (Symbolic_label.end_stmt stmt.sid) ;
      if insert_something_after then Format.fprintf fmt "@]@\n}@\n" ;
      Format.pp_close_box fmt () ;
      Format.pp_close_box fmt ()

    method! file fmt f =
      self#headers fmt ;
      let is_gfun = function GFun _ -> true | _ -> false in
      Cil.iterGlobals f (fun g -> if not (is_gfun g) then self#global fmt g) ;
      Cil.iterGlobals f (fun g -> if is_gfun g then self#global fmt g)

    method private headers fmt =
      let is_nondet b i = b || Utils.is_stmt_nondet i in
      let on_hash _ (_, q, _) b = b || Queue.fold is_nondet b q in
      let on_func b f = b || Utils.is_fundec_nondet f in
      let nondet = Hashtbl.fold on_hash insertions false in
      let nondet = List.fold_left on_func nondet functions in
      let externals_file = Options.Share.file ~error:true "externals.h" in
      let nondet_file = Options.Share.file ~error:true "nondet.c" in
      Format.fprintf fmt "#include \"%s\"@\n" externals_file ;
      if nondet then Format.fprintf fmt "#include \"%s\"@\n" nondet_file ;
      Format.fprintf fmt "@\n"

    val mutable first_global = true

    method! global fmt g =
      match g with
      | GFun (fundec, l) ->
          if first_global then (
            List.iter (fun x -> self#generated_fundecl fmt x) functions ;
            first_global <- false ) ;
          let oldattr = fundec.svar.vattr in
          (fundec.svar).vattr <- [] ;
          self#line_directive ~forcefile:true fmt l ;
          self#fundecl fmt fundec ;
          (fundec.svar).vattr <- oldattr ;
          Format.fprintf fmt "@\n"
      | GVar (vi, _, _) ->
          let old_vghost = vi.vghost in
          vi.vghost <- false ;
          super#global fmt g ;
          vi.vghost <- old_vghost
      | _ -> super#global fmt g
  end
