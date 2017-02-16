
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

let loc = Cil_datatype.Location.unknown

let split_decl_instr l =
  List.fold_left (fun (decl,instr) i ->
    match i with
    | Decl v -> (v :: decl,instr)
    | _ -> (decl, i::instr)
  ) ([],[]) l

let rec to_stmt = function
  | Instru i -> Cil.mkStmt (Instr i)
  | IRet e -> Cil.mkStmt (Return (Some e, loc))
  | Decl _ -> assert false
  | IBlock i -> Cil.mkStmt (Block (ilist_to_block i))
  | IIf (e, b1, b2) ->
     Cil.mkStmt (If(e, ilist_to_block b1, ilist_to_block b2, loc))
  | ILoop (e, b) ->
     let break_stmt = Cil.mkStmt (Break loc) in
     let b1 = Cil.mkBlock [] and b2 = Cil.mkBlock [break_stmt] in
     let i = Cil.mkStmt (If(e, b1, b2, loc)) in
     let b' = ilist_to_block b in
     Cil.mkStmt (Loop ([], {b' with bstmts = i :: b'.bstmts}, loc, None, None))
       
and ilist_to_block il =
  let vars, instr = split_decl_instr il in
  {battrs=[]; blocals=(List.rev vars); bstmts=List.map to_stmt (List.rev instr)}

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

let pretty fmt ins =
  match ins with
  | Decl v ->
     let ty = Cil.stripConstLocalType v.vtype in
     let array_to_ptr = function TArray(t,_,_,a) -> TPtr(t,a) | t -> t in
     let ty = array_to_ptr ty in
     let v' = {v with vtype = ty} in
     Format.fprintf fmt "@[%a;@]@\n" (new Printer.extensible_printer())#vdecl v'
  | _ -> Format.fprintf fmt "@[%a@]@\n" Printer.pp_stmt (to_stmt ins)
