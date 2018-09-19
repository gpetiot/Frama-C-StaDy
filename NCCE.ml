type var_state = string * string * string

type var_states = var_state Datatype.String.Hashtbl.t

type t = Property.t * string * string * var_states

let all_for prop =
  let on_nc k (a, b) acc = (prop, k, a, b) :: acc in
  try
    let t = States.NC_counter_examples.find prop in
    Datatype.String.Hashtbl.fold on_nc t []
  with Not_found -> []

let one_for prop =
  let on_nc k (a, b) = function None -> Some (prop, k, a, b) | x -> x in
  try
    let t = States.NC_counter_examples.find prop in
    Datatype.String.Hashtbl.fold on_nc t None
  with Not_found -> None

let register ignore_var kind prop str_tc msg list_entries =
  let file_tbl =
    try States.NC_counter_examples.find prop with Not_found ->
      Datatype.String.Hashtbl.create 16
  in
  let msg, var_tbl =
    try Datatype.String.Hashtbl.find file_tbl str_tc with Not_found ->
      (msg, Datatype.String.Hashtbl.create 16)
  in
  let on_pair (var, value) =
    let i, c, s =
      try Datatype.String.Hashtbl.find var_tbl var with Not_found ->
        ("", "", "")
    in
    let i, c, s =
      if kind = "IN" then (value, c, s)
      else if kind = "OUTCONC" then (i, value, s)
      else (i, c, value)
    in
    if ignore_var var then ()
    else Datatype.String.Hashtbl.replace var_tbl var (i, c, s)
  in
  List.iter on_pair list_entries ;
  Datatype.String.Hashtbl.replace file_tbl str_tc (msg, var_tbl) ;
  States.NC_counter_examples.replace prop file_tbl

let pretty fmt (p, f, msg, var_states) =
  let pp_msg fmt = function "" -> () | x -> Format.fprintf fmt "(%s)" x in
  let pp_loc = Cil_datatype.Location.pretty in
  let on_var var (input, con, sym) =
    match (con, sym) with
    | "", "" -> Format.fprintf fmt "%s = %s@\n" var input
    | "", x | x, "" ->
        if input = "" then Format.fprintf fmt "%s = %s@\n" var x
        else Format.fprintf fmt "%s = %s (in) ; %s (out)@\n" var input x
    | x, y ->
        if input = "" then
          if x = y then Format.fprintf fmt "%s = %s@\n" var x
          else
            Format.fprintf fmt "%s = %s (concrete) ; %s (symbolic)@\n" var x y
        else if x = y then
          Format.fprintf fmt "%s = %s (in) ; %s (out)@\n" var input x
        else
          Format.fprintf fmt
            "%s = %s (in) ; %s (concrete out) ; %s (symbolic out)@\n" var input
            x y
  in
  Format.fprintf fmt "Non-Compliance@\n" ;
  Format.fprintf fmt "of       : @[%a@] %a@\n" Property.pretty p pp_msg msg ;
  Format.fprintf fmt "location : @[%a@]@\n" pp_loc (Property.location p) ;
  Format.fprintf fmt "TEST DRIVER: %s@\n" f ;
  Datatype.String.Hashtbl.iter_sorted on_var var_states
