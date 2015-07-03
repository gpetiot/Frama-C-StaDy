
(* Extend the default printer to display the generated code insertions
 * at the corresponding label and the generated functions. *)
class print_insertions:
	(* labeled code insertions *)
	(Symbolic_label.t, Insertion.t Queue.t) Hashtbl.t ->
	(* new functions *)
	Function.t list ->
	(* id of stmts, parameterizing the SWD *)
	int list ->
	Printer.extensible_printer
