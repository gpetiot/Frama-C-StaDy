type t

val all_for : Property.t -> t list

val one_for : Property.t -> t option

val register :
     (string -> bool)
  -> string
  -> Property.t
  -> string
  -> string
  -> (string * string) list
  -> unit

val pretty : Format.formatter -> t -> unit
