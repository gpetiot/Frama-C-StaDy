type t

(* constructors *)
val beg_stmt : int -> t

val end_stmt : int -> t

val beg_func : string -> t

val end_func : string -> t

val beg_iter : int -> t

val end_iter : int -> t

(* pretty-printing *)
val pretty : Format.formatter -> t -> unit
