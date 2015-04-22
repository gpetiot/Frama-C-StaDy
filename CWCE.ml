
open Cil_types

type var_state = string * string * string
type var_states = var_state Datatype.String.Hashtbl.t
type t = Property.t * string * string * stmt list * var_states


let all_for prop =
  let on_cw k (a,b,c) acc = ((prop,k,a,b,c)::acc) in
  try
    let t = States.CW_counter_examples.find prop in
    Datatype.String.Hashtbl.fold on_cw t []
  with Not_found -> []


let one_for prop =
  let on_cw k (a,b,c) = function None -> Some (prop,k,a,b,c) | x -> x in
  try
    let t = States.CW_counter_examples.find prop in
    Datatype.String.Hashtbl.fold on_cw t None
  with Not_found -> None


let pretty fmt (p, f, msg, stmts, var_states) =
  let pp_msg fmt = function "" -> () | x -> Format.fprintf fmt "(%s)" x in
  let pp_loc = Cil_datatype.Location.pretty in
  let pp_stmt fmt s = match s.skind with
    | Instr(Call _) -> Printer.pp_stmt fmt s
    | _ -> Format.fprintf fmt "stmt %i" s.sid
  in
  let on_var var (inp, con, sym) =
    match con, sym with
    | "", "" -> Format.fprintf fmt "%s = %s@\n" var inp
    | "", x
    | x, "" -> Format.fprintf fmt "%s = %s -- OUTPUT: %s@\n" var inp x
    | x, y -> Format.fprintf fmt "%s = %s -- OUTPUT: %s (%s)@\n" var inp x y
  in
  Format.fprintf
    fmt "CW of @[%a@] for @[%a@] %a@\n"
    (Pretty_utils.pp_list pp_stmt) stmts Property.pretty p pp_msg msg;
  let on_stmt s =
    Format.fprintf fmt "LOCATION: %a@\n" pp_loc (Cil_datatype.Stmt.loc s)
  in
  List.iter on_stmt stmts;
  Format.fprintf fmt "TEST DRIVER: %s@\n" f;
  Datatype.String.Hashtbl.iter_sorted on_var var_states
