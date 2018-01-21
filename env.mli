
type t

val empty : t

(* Tip: Put the shorter env first *)
val merge : t -> t -> t

val make : Cil_types.varinfo list ->
  Cil_types.stmt list ->
  Cil_types.stmt list -> t

val mk_if : Cil_types.exp -> t -> t -> Cil_types.stmt
val mk_block : t -> Cil_types.stmt
val mk_loop : Cil_types.exp -> t -> Cil_types.stmt

val locals : t -> Cil_types.varinfo list
val stmts : t -> Cil_types.stmt list
val cleans : t -> Cil_types.stmt list
