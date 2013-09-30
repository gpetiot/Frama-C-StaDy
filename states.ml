
module TestFailures = State_builder.Hashtbl
  (Property.Hashtbl)
  (Datatype.List
     (Datatype.Pair
	(Datatype.String) (* C testcase filename *)
	(Datatype.List  (* entries *)
	   (Datatype.Pair (Datatype.String) (Datatype.String))
	)
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

