
type t

val all_for : Property.t -> t list
val one_for : Property.t -> t option
val pretty : Format.formatter -> t -> unit
