
val machdep: unit -> int

val typically_preds: Cil_types.behavior -> Cil_types.identified_predicate list

val to_id: States.Property_To_Id.key -> States.Property_To_Id.data

val to_prop: States.Id_To_Property.key -> States.Id_To_Property.data

val get_var_desc:
  States.Var_Descriptions.key -> States.Var_Descriptions.data

val unname: Cil_types.typ -> Cil_types.typ

val extract_guards:
  Cil_datatype.Logic_var.t ->
  Cil_types.predicate ->
  Cil_types.term * Cil_types.relation * Cil_types.relation * Cil_types.term

val error_term: Cil_types.term -> 'a
val error_toffset: Cil_types.term_offset -> 'a

val mpz_t: unit -> Cil_types.typ

val binop_to_relation: Cil_types.binop -> Cil_types.relation
val binop_to_fname: Cil_types.binop -> string

val relation_to_binop: Cil_types.relation -> Cil_types.binop
val relation_to_string: Cil_types.relation -> string

val default_behavior: Cil_types.kernel_function -> Cil_types.behavior

val initialize: unit -> unit
val finalize: unit -> unit
