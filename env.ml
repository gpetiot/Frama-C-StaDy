open Cil_types

type t = Cil_types.varinfo list * Cil_types.stmt list * Cil_types.stmt list

let empty = ([], [], [])

let merge (v1, s1, c1) (v2, s2, c2) =
  ( List.rev_append (List.rev v1) v2
  , List.rev_append (List.rev s1) s2
  , List.rev_append (List.rev c1) c2 )

let make v s c = (v, s, c)

let loc = Cil_datatype.Location.unknown

let mk_if e (v1, s1, c1) (v2, s2, c2) =
  let b1 = Cil.mkBlock (List.rev_append (List.rev s1) c1)
  and b2 = Cil.mkBlock (List.rev_append (List.rev s2) c2) in
  Cil.mkStmt (If (e, {b1 with blocals= v1}, {b2 with blocals= v2}, loc))

let mk_block (v, s, c) =
  let b = Cil.mkBlock (List.rev_append (List.rev s) c) in
  Cil.mkStmt (Block {b with blocals= v})

let mk_loop e (v, s, c) =
  let break_stmt = Cil.mkStmt (Break loc) in
  let b1 = Cil.mkBlock [] and b2 = Cil.mkBlock [break_stmt] in
  let i = Cil.mkStmt (If (e, b1, b2, loc)) in
  let b = Cil.mkBlock (List.rev_append (List.rev s) c) in
  let b = {b with blocals= v} in
  Cil.mkStmt (Loop ([], {b with bstmts= i :: b.bstmts}, loc, None, None))

let locals (v, _s, _c) = v

let stmts (_v, s, _c) = s

let cleans (_v, _s, c) = c
