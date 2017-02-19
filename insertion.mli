
type t

val mk_instru : Cil_types.instr -> t
val mk_ret : Cil_types.exp -> t
val mk_decl : Cil_types.varinfo -> t
val mk_block : t list -> t
val mk_if : Cil_types.exp -> t list -> t list -> t
val mk_loop : Cil_types.exp -> t list -> t

val is_stmt_nondet : Cil_types.stmt -> bool
val is_nondet : t -> bool

val split_decl_instr : t list -> Cil_types.varinfo list * t list
val to_stmt : t -> Cil_types.stmt

val pretty : Format.formatter -> t -> unit
val pretty_var : Format.formatter -> Cil_types.varinfo -> unit
