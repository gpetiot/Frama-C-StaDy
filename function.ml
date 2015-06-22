
open Cil_types

type t = {
  mutable func_var: varinfo;
  mutable func_formals: varinfo list;
  mutable func_locals: varinfo list;
  mutable func_stmts: Insertion.t list;
}

let make v f l s = {func_var=v; func_formals=f; func_locals=l; func_stmts=s;}

let pretty fmt f =
  let ty = f.func_var.vtype in
  Format.fprintf fmt "@[<v 2>%a {@\n" Printer.pp_typ ty;
  let rec aux = function
    | [] -> ()
    | [h] -> Format.fprintf fmt "%a" (Insertion.pretty ~line_break:false) h
    | h::t ->
       Format.fprintf fmt "%a" (Insertion.pretty ~line_break:true) h;
       aux t
  in
  aux f.func_stmts;
  Format.fprintf fmt "@]@\n}@\n"

let pretty_header fmt f =
  let ty = f.func_var.vtype in
  Format.fprintf fmt "@[%a;@\n@]" Printer.pp_typ ty

let is_nondet f =
  let is_nondet b i = b || Insertion.is_nondet i in
  List.fold_left is_nondet false f.func_stmts
