type label =
  | BegStmt of int
  | EndStmt of int
  | BegFunc of string
  | EndFunc of string
  | BegIter of int
  | EndIter of int

type t = label

let beg_stmt x = BegStmt x

let end_stmt x = EndStmt x

let beg_func x = BegFunc x

let end_func x = EndFunc x

let beg_iter x = BegIter x

let end_iter x = EndIter x

let pretty fmt = function
  | BegStmt s -> Format.fprintf fmt "BegStmt %i" s
  | EndStmt s -> Format.fprintf fmt "EndStmt %i" s
  | BegFunc s -> Format.fprintf fmt "BegFunc %s" s
  | EndFunc s -> Format.fprintf fmt "EndFunc %s" s
  | BegIter s -> Format.fprintf fmt "BegIter %i" s
  | EndIter s -> Format.fprintf fmt "EndIter %i" s
