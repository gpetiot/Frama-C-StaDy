
type t

val mk_instru : Cil_types.instr -> t
val mk_ret : Cil_types.exp -> t
val mk_decl : Cil_types.varinfo -> t
val mk_block : t list -> t
val mk_if : Cil_types.exp -> t list -> t list -> t
val mk_loop : Cil_types.exp -> t list -> t

val is_stmt_nondet : Cil_types.stmt -> bool
val is_fundec_nondet : Cil_types.fundec -> bool

val to_cil : t -> Cil_types.varinfo list * Cil_types.stmt list
val list_to_cil : t list -> Cil_types.varinfo list * Cil_types.stmt list

val pretty_var : Format.formatter -> Cil_types.varinfo -> unit
