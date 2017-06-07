
open Cil_types

type var_state = string * string * string
type var_states = var_state Datatype.String.Hashtbl.t
type t = Property.t * string * string * stmt list * var_states


let all_for prop =
  let on_sw k (a,b,c) acc = ((prop,k,a,b,c)::acc) in
  try
    let t = States.SW_counter_examples.find prop in
    Datatype.String.Hashtbl.fold on_sw t []
  with Not_found -> []


let one_for prop =
  let on_sw k (a,b,c) = function None -> Some (prop,k,a,b,c) | x -> x in
  try
    let t = States.SW_counter_examples.find prop in
    Datatype.String.Hashtbl.fold on_sw t None
  with Not_found -> None


let register ignore_var kind prop str_tc msg stmts list_entries =
  let file_tbl =
    try States.SW_counter_examples.find prop
    with Not_found -> Datatype.String.Hashtbl.create 16
  in
  let msg, stmts, var_tbl =
    try Datatype.String.Hashtbl.find file_tbl str_tc
    with Not_found -> msg, stmts, Datatype.String.Hashtbl.create 16
  in
  let on_pair (var, value) =
    let i, c, s =
      try Datatype.String.Hashtbl.find var_tbl var
      with Not_found -> "", "", ""
    in
    let i, c, s =
      if kind = "IN" then value,c,s
      else if kind = "OUTCONC" then i,value,s
      else i,c,value
    in
    if ignore_var var then ()
    else Datatype.String.Hashtbl.replace var_tbl var (i,c,s)
  in
  List.iter on_pair list_entries;
  Datatype.String.Hashtbl.replace file_tbl str_tc (msg, stmts, var_tbl);
  States.SW_counter_examples.replace prop file_tbl


let pretty fmt (p, f, msg, stmts, var_states) =
  let pp_msg fmt = function "" -> () | x -> Format.fprintf fmt "(%s)" x in
  let pp_loc = Cil_datatype.Location.pretty in
  let pp_stmt fmt s =
    let label = match List.hd s.labels with
      | Label (str,_,_) -> str
      | _ -> assert false (* unreachable *)
    in
    let pp_descr fmt s = match s.skind with
      | Loop _ -> Format.fprintf fmt "loop"
      | Instr (Call (_,f,_,_)) ->
	 Format.fprintf fmt "'%a' call" Printer.pp_exp f
      | _ -> assert false (* unreachable *)
    in
    Format.fprintf fmt "%a at label '%s'" pp_descr s label
  in
  let on_var var (input, con, sym) =
    match con, sym with
    | "", "" -> Format.fprintf fmt "%s = %s@\n" var input
    | "", x
    | x, "" ->
       if input = "" then
	 Format.fprintf fmt "%s = %s@\n" var x
       else
	 Format.fprintf fmt "%s = %s (in) ; %s (out)@\n" var input x
    | x, y ->
       if input = "" then
	 if x = y then
	   Format.fprintf fmt "%s = %s@\n" var x
	 else
	   Format.fprintf fmt "%s = %s (concrete) ; %s (symbolic)@\n" var x y
       else
	 if x = y then
	   Format.fprintf fmt "%s = %s (in) ; %s (out)@\n" var input x
	 else
	   Format.fprintf fmt
	     "%s = %s (in) ; %s (concrete out) ; %s (symbolic out)@\n"
	     var input x y
  in
  Format.fprintf fmt "Subcontract Weakness@\n";
  let on_stmt s =
    Format.fprintf fmt "of       : @[%a@]@\n" pp_stmt s;
    Format.fprintf fmt "location : @[%a@]@\n" pp_loc (Cil_datatype.Stmt.loc s)
  in
  List.iter on_stmt stmts;
  Format.fprintf fmt "for      : @[%a@] %a@\n" Property.pretty p pp_msg msg;
  Format.fprintf fmt "location : @[%a@]@\n" pp_loc (Property.location p);
  Format.fprintf fmt "TEST DRIVER: %s@\n" f;
  Datatype.String.Hashtbl.iter_sorted on_var var_states
