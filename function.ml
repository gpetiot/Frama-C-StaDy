
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
  let vname = f.func_var.vname in
  let print fmt = Format.fprintf fmt "%s" vname in
  Format.fprintf
    fmt "@[<v 2>%a {@\n" ((new Unname.printer ())#typ (Some print)) ty;
  List.iter (Insertion.pretty fmt) f.func_stmts;
  Format.fprintf fmt "@]@\n}@\n"

let pretty_header fmt f =
  let ty = f.func_var.vtype in
  let vname = f.func_var.vname in
  let print fmt = Format.fprintf fmt "%s" vname in
  Format.fprintf fmt "@[%a;@\n@]" ((new Unname.printer ())#typ (Some print)) ty

let is_nondet f =
  let is_nondet b i = b || Insertion.is_nondet i in
  List.fold_left is_nondet false f.func_stmts
