
class printer () = object
  inherit Printer.extensible_printer () as super

  val mutable in_vdecl = 0

  method! vdecl fmt v =
    in_vdecl <- in_vdecl+1; super#vdecl fmt v; in_vdecl <- in_vdecl-1

  (* "unname" all types, except in a variable declaration *)
  method! typ ?fundecl fmtopt fmt t =
    super#typ ?fundecl fmtopt fmt (if in_vdecl > 0 then t else (Utils.unname t))
end
