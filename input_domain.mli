
type pl_domain
type pl_rel
type pl_quantif


val compute_constraints: unit -> pl_domain list * pl_rel list * pl_quantif list

val add_global: pl_domain list -> Cil_types.varinfo -> pl_domain list

val add_init_global: pl_domain list -> Cil_types.varinfo -> pl_domain list

val translate: string ->
	       pl_domain list ->
	       pl_rel list ->
	       pl_quantif list ->
	       unit
