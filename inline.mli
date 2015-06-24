
type env

val empty_env : env
val pred : env -> Cil_types.predicate -> Cil_types.predicate
val pnamed : env -> Cil_types.predicate Cil_types.named ->
	     Cil_types.predicate Cil_types.named
val id_pred : env -> Cil_types.identified_predicate ->
	      Cil_types.identified_predicate
