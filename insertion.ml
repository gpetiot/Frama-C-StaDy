
open Cil_types

type insertion =
  | Instru of instr
  | IRet of exp
  | Decl of varinfo
  | IBlock of insertion list
  | IIf of exp * insertion list * insertion list
  | ILoop of exp * insertion list

type t = insertion

let mk_instru i = Instru i
let mk_ret a = IRet a
let mk_decl v = Decl v
let mk_block b = IBlock b
let mk_if a b c = IIf (a, b, c)
let mk_loop a b = ILoop (a, b)

let rec is_nondet = function
  | Instru(Call (_,{enode=Lval(Var v,_)},_,_)) ->
     begin try (String.sub v.vname 0 7) = "nondet_" with _ -> false end
  | Instru _ -> false
  | IRet _ -> false
  | Decl _ -> false
  | IBlock i -> is_nondet_list i
  | IIf (_, i1, i2) -> is_nondet_list (List.rev_append i1 i2)
  | ILoop (_, i) -> is_nondet_list i
and is_nondet_list = function
  | [] -> false
  | h :: _ when is_nondet h -> true
  | _ :: t -> is_nondet_list t

let rec pretty ?(line_break = true) fmt ins =
  begin
    match ins with
    | Instru i -> Format.fprintf fmt "@[%a@]" Printer.pp_instr i
    | IRet e -> Format.fprintf fmt "@[return %a;@]" Printer.pp_exp e
    | Decl v ->
       let ty = Cil.stripConstLocalType v.vtype in
       let array_to_ptr = function TArray(t,_,_,a) -> TPtr(t,a) | t -> t in
       let ty = array_to_ptr ty in
       let v' = {v with vtype = ty} in
       Format.fprintf fmt "@[%a;@]" (new Printer.extensible_printer())#vdecl v'
    | IBlock b ->
       if b <> [] then Format.fprintf fmt "@[<hov 2>{@\n%a@]@\n}" aux b
    | IIf (e,b1,b2) ->
       let print_if() =
	 Format.fprintf
	   fmt "@[<hov 2>if(%a) {@\n%a@]@\n}" Printer.pp_exp e aux b1;
	 if b2 <> [] then
	   Format.fprintf fmt "@\n@[<hov 2>else {@\n%a@]@\n}" aux b2
       in
       begin
	 match Cil.isInteger e with
	 | None -> print_if()
	 | Some i ->
	    if Integer.equal i Integer.zero then
	      (if b2 <> [] then
		  Format.fprintf fmt "@[<hov 2>{@\n%a@]@\n}" aux b2)
	    else if Integer.equal i Integer.one then
	      (if b1 <> [] then
		  Format.fprintf fmt "@[<hov 2>{@\n%a@]@\n}" aux b1)
	    else print_if()
       end
    | ILoop (e,b) ->
       Format.fprintf
	 fmt "@[<hov 2>while(%a) {@\n%a@]@\n}" Printer.pp_exp e aux b
  end;
  if line_break then Format.fprintf fmt "@\n"
and aux fmt = function
  | [] -> ()
  | [ h ] -> pretty ~line_break:false fmt h
  | h :: t -> pretty fmt h; aux fmt t
