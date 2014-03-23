
module TestFailures =
  State_builder.Hashtbl
    (Property.Hashtbl)
    (Datatype.String.Hashtbl.Make
       (Datatype.Triple
	  (* input *)
	  (Datatype.List (Datatype.Pair (Datatype.String) (Datatype.String)))

	  (* concrete output *)
	  (Datatype.List (Datatype.Pair (Datatype.String) (Datatype.String)))

	  (* symbolic output *)
	  (Datatype.List (Datatype.Pair (Datatype.String) (Datatype.String)))
       )
    )
    (struct
      let name = "PathCrawler.TestFailures"
      let dependencies = [Ast.self]
      let size = 64
     end)
  

module NbCases = State_builder.Zero_ref
  (struct
    let name = "PathCrawler.NbCases"
    let dependencies = [Ast.self]
   end)

module All_Paths = State_builder.False_ref
  (struct
    let name = "PathCrawler.All_Paths"
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
