
val machdep: unit -> int

val typically_preds: Cil_types.behavior -> Cil_types.identified_predicate list

val to_id: States.Property_To_Id.key -> States.Property_To_Id.data

val to_prop: States.Id_To_Property.key -> States.Id_To_Property.data

(* for OCaml < 4.04.0 *)
val split: char -> string -> string list

val unname: Cil_types.typ -> Cil_types.typ

val extract_guards:
  Cil_datatype.Logic_var.t ->
  Cil_types.predicate ->
  Cil_types.term option
  * Cil_types.relation option
  * Cil_types.relation option
  * Cil_types.term option

val mk_fundec: Cil_types.varinfo -> formals:Cil_types.varinfo list ->
  locals:Cil_types.varinfo list -> Cil_types.stmt list -> Cil_types.fundec

val error_term: Cil_types.term -> 'a
val error_toffset: Cil_types.term_offset -> 'a

val mpz_t: unit -> Cil_types.typ

val binop_to_relation: Cil_types.binop -> Cil_types.relation
val binop_to_fname: Cil_types.binop -> string

val relation_to_binop: Cil_types.relation -> Cil_types.binop
val relation_to_string: Cil_types.relation -> string

val default_behavior: Cil_types.kernel_function -> Cil_types.behavior

val loop_condition: Cil_types.stmt -> Cil_types.exp

val is_stmt_nondet : Cil_types.stmt -> bool
val is_fundec_nondet : Cil_types.fundec -> bool

val pretty_var : Format.formatter -> Cil_types.varinfo -> unit

val initialize: unit -> unit
val finalize: unit -> unit

val typename : Cil_types.typ -> string
val type_of_pointed : Cil_types.logic_type -> Cil_types.logic_type
