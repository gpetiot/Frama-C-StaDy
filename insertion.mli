
type t

val mk_instru : Cil_types.instr -> t
val mk_ret : Cil_types.exp -> t
val mk_decl : Cil_types.varinfo -> t
val mk_block : t list -> t
val mk_if : Cil_types.exp -> t list -> t list -> t
val mk_loop : Cil_types.exp -> t list -> t

val is_nondet : t -> bool

val pretty : ?line_break:bool -> Format.formatter -> t -> unit
