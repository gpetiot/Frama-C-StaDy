
val machdep: unit -> int

val typically_preds: ('a, 'b) Cil_types.behavior -> 'a list

val to_id: States.Property_To_Id.key -> States.Property_To_Id.data

val to_prop: States.Id_To_Property.key -> States.Id_To_Property.data

val unname: Cil_types.typ -> Cil_types.typ

val extract_guards:
  Cil_datatype.Logic_var.t ->
  Cil_types.predicate Cil_types.named ->
  Cil_types.term * Cil_types.relation * Cil_types.relation * Cil_types.term

val error_term: Cil_types.term -> 'a
val error_toffset: Cil_types.term_offset -> 'a

val mpz_t_ref: Cil_types.typ option ref
val mpz_t: unit -> Cil_types.typ

val binop_to_relation: Cil_types.binop -> Cil_types.relation
val binop_to_fname: Cil_types.binop -> string

val relation_to_binop: Cil_types.relation -> Cil_types.binop
val rel_to_string: Cil_types.relation -> string
