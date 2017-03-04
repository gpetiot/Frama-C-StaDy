
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
  let f (decl,instr) = function
    | Decl v -> (v :: decl, instr)
    | i -> (decl, i::instr)
  in
  List.fold_left f ([],[]) l

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

let to_cil = function
  | Decl v -> [v], []
  | i -> [], [to_stmt i]

let list_to_cil ins =
  let f (vs, ss) i =
    let v, s = to_cil i in
    List.rev_append v vs, List.rev_append s ss
  in
  let vars, stmts = List.fold_left f ([], []) ins in
  List.rev vars, List.rev stmts

let rec is_stmt_nondet stmt = match stmt.skind with
  | Instr (Call (_,{enode=Lval(Var v,_)},_,_)) ->
     begin try (String.sub v.vname 0 7) = "nondet_" with _ -> false end
  | If (_, b1, b2, _) ->
     if List.fold_left (fun acc s -> acc || is_stmt_nondet s) false b1.bstmts
     then
       true
     else List.fold_left (fun acc s -> acc || is_stmt_nondet s) false b2.bstmts
  | Loop (_, b, _, _, _) ->
     List.fold_left (fun acc s -> acc || is_stmt_nondet s) false b.bstmts
  | _ -> false

let is_fundec_nondet f =
  let is_nondet b i = b || is_stmt_nondet i in
  List.fold_left is_nondet false f.sbody.bstmts

let pretty_var fmt v =
  let ty = Cil.stripConstLocalType v.vtype in
  let array_to_ptr = function TArray(t,_,_,a) -> TPtr(t,a) | t -> t in
  let ty = array_to_ptr ty in
  let v' = {v with vtype = ty} in
  Format.fprintf fmt "@[%a;@]@\n" (new Printer.extensible_printer())#vdecl v'
 
