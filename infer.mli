(* Computes and returns a hashtable such that :
   - var1 => inferred size for var1
   - var2 => inferred size for var2
   - ...
   - var n => inferred size for varn *)
val lengths_from_requires :
  Kernel_function.t -> Cil_types.term list Cil_datatype.Varinfo.Hashtbl.t
