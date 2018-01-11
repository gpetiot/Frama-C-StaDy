
(* input, concrete output, symbolic output *)
module Var_state =
  Datatype.Triple (Datatype.String) (Datatype.String) (Datatype.String)

module Var_states = Datatype.String.Hashtbl.Make (Var_state)

module NC_counter_examples =
  State_builder.Hashtbl
    (Property.Hashtbl)
    (Datatype.String.Hashtbl.Make (* file *)
       (Datatype.Pair
	  (Datatype.String) (* msg *)
	  (Var_states)
       )
    )
    (struct
      let name = "NC_counter_examples"
      let dependencies = [Ast.self]
      let size = 16
     end)

module Stmt_list = Datatype.List (Cil_datatype.Stmt)

module SW_counter_examples =
  State_builder.Hashtbl
    (Property.Hashtbl)
    (Datatype.String.Hashtbl.Make (* file *)
       (Datatype.Triple
	  (Datatype.String) (* msg *)
	  (Stmt_list) (* statements whose contract is too weak *)
	  (Var_states)
       )
    )
    (struct
      let name = "SW_counter_examples"
      let dependencies = [Ast.self]
      let size = 16
     end)

module Nb_test_cases = State_builder.Zero_ref
  (struct
    let name = "Nb_test_cases"
    let dependencies = [Ast.self]
   end)

module All_Paths = State_builder.False_ref
  (struct
    let name = "All_Paths"
    let dependencies = [Ast.self]
   end)

module Property_To_Id =
  State_builder.Hashtbl
    (Property.Hashtbl)
    (Datatype.Int)
    (struct
      let name = "Property_To_Id"
      let dependencies = [Ast.self]
      let size = 64
     end)

module Id_To_Property =
  State_builder.Hashtbl
    (Datatype.Int.Hashtbl)
    (Property)
    (struct
      let name = "Id_To_Property"
      let dependencies = [Ast.self]
      let size = 64
     end)

module Not_Translated_Predicates =
  State_builder.List_ref (Datatype.Int)
    (struct
      let name = "Not_Translated_Predicates"
      let dependencies = [Ast.self]
     end)

module Externals =
  State_builder.Hashtbl
    (Datatype.String.Hashtbl)
    (Cil_datatype.Varinfo)
    (struct
      let name = "Externals"
      let dependencies = [Ast.self]
      let size = 64
     end)

