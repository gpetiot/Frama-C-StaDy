
val pp_term: Format.formatter -> Cil_types.term -> unit
val pp_toffset: Format.formatter -> Cil_types.term_offset -> unit
val pp_pred: Format.formatter -> Cil_types.predicate -> unit
val pp_list: ?sep:string -> (Format.formatter -> 'a -> unit) ->
	     Format.formatter -> 'a list -> unit
