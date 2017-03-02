
type t

val make: Cil_types.varinfo -> formals:Cil_types.varinfo list ->
  locals:Cil_types.varinfo list -> Cil_types.stmt list -> t
val pretty: Format.formatter -> t -> unit
val is_nondet: t -> bool
