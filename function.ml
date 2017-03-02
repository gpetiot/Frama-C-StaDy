
open Cil_types

type t = {
  mutable var: varinfo;
  mutable formals: varinfo list;
  mutable locals: varinfo list;
  mutable stmts: Insertion.t list;
}

let make v ~formals ~locals s = {var=v; formals; locals; stmts=s;}

let pretty fmt f =
  let print fmt = Format.fprintf fmt "%s" f.var.vname in
  Format.fprintf fmt "@[<v 2>%a {@\n"
    ((new Printer.extensible_printer ())#typ (Some print)) f.var.vtype ;
  List.iter (Insertion.pretty fmt) f.stmts;
  Format.fprintf fmt "@]@\n}@\n"

let is_nondet f =
  let is_nondet b i = b || Insertion.is_nondet i in
  List.fold_left is_nondet false f.stmts
