
(* Appends an element to the end of a list. *)
let append_end : 'a list -> 'a -> 'a list =
  fun l elt -> List.rev_append (List.rev l) [elt]

let no_repeat : 'a list -> 'a list =
  fun l ->
    let rec aux acc = function
      | [] -> acc
      | h :: t when List.mem h acc -> aux acc t
      | h :: t -> aux (h :: acc) t
    in
    aux  [] l

let comma : string -> string -> string =
  fun x y -> if x = "" then y else (x ^ ", " ^ y)

let fold_comma : string list -> string =
  fun l -> List.fold_left comma "" l

let fieldinfo_to_int : Cil_types.fieldinfo -> Integer.t =
  fun fi ->
    let rec aux cpt = function
      | {Cil_types.forig_name=s}::_ when s = fi.Cil_types.forig_name ->
	Integer.of_int cpt
      | _::t -> aux (cpt+1) t
      | _ -> assert false
    in
    aux 0 fi.Cil_types.fcomp.Cil_types.cfields

let machdep : unit -> int =
  fun () ->
    match Kernel.Machdep.get() with
    | "x86_64" -> 64
    | "x86_32" | "ppc_32" -> 32
    | "x86_16" -> 16
    | _ -> 32
