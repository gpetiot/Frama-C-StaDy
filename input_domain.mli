
type pl_constraint


val compute_constraints: unit -> pl_constraint list

val add_global: pl_constraint list -> Cil_types.varinfo -> pl_constraint list

val add_init_global:
  pl_constraint list -> Cil_types.varinfo -> pl_constraint list

val translate: string -> pl_constraint list -> unit
