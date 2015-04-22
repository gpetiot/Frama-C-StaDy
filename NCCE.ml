
type var_state = string * string * string
type var_states = var_state Datatype.String.Hashtbl.t
type t = Property.t * string * string * var_states


let all_for prop =
  let on_nc k (a,b) acc = ((prop,k,a,b)::acc) in
  try
    let t = States.NC_counter_examples.find prop in
    Datatype.String.Hashtbl.fold on_nc t []
  with Not_found -> []


let one_for prop =
  let on_nc k (a,b) = function None -> Some (prop,k,a,b) | x -> x in
  try
    let t = States.NC_counter_examples.find prop in
    Datatype.String.Hashtbl.fold on_nc t None
  with Not_found -> None


let pretty fmt (p, f, msg, var_states) =
  let pp_msg fmt = function "" -> () | x -> Format.fprintf fmt "(%s)" x in
  let pp_loc = Cil_datatype.Location.pretty in
  let on_var var (inp, con, sym) =
    match con, sym with
    | "", "" -> Format.fprintf fmt "%s = %s@\n" var inp
    | "", x
    | x, "" -> Format.fprintf fmt "%s = %s -- OUTPUT: %s@\n" var inp x
    | x, y -> Format.fprintf fmt "%s = %s -- OUTPUT: %s (%s)@\n" var inp x y
  in
  Format.fprintf fmt "NC of @[%a@] %a@\n" Property.pretty p pp_msg msg;
  Format.fprintf fmt "LOCATION: %a@\n" pp_loc (Property.location p);
  Format.fprintf fmt "TEST DRIVER: %s@\n" f;
  Datatype.String.Hashtbl.iter_sorted on_var var_states
