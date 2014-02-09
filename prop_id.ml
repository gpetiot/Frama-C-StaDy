

let id_to_prop_tbl : Property.t Datatype.Int.Hashtbl.t =
  Datatype.Int.Hashtbl.create 32
let prop_to_id_tbl : int Property.Hashtbl.t =
  Property.Hashtbl.create 32


let to_id prop = Property.Hashtbl.find prop_to_id_tbl prop

let to_prop id = Datatype.Int.Hashtbl.find id_to_prop_tbl id


(* we can only modify the property_status of the properties that have really
   been translated into pathcrawler_assert_exception *)
let translated_properties = ref ([] : Property.t list)


let all_paths = ref false
let typically = ref ([] : Property.identified_property list)
