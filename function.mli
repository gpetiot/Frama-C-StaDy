
type t

val make: Cil_types.varinfo -> Cil_types.varinfo list ->
	  Cil_types.varinfo list -> Insertion.t list -> t
val pretty: Format.formatter -> t -> unit
val is_nondet: t -> bool
