
val translate:
  Property.t list ->
  int list ->
  (
    (* labeled code insertions *)
    (Symbolic_label.t, Insertion.t Queue.t) Hashtbl.t
    (* generated functions *)
    * Function.t list
    (* translated properties *)
    * Property.t list
    (* new globals (for PathCrawler) *)
    * Cil_types.varinfo list
    (* new initialized globals (for PathCrawler) *)
    * Cil_types.varinfo list
  )
