open Cil_types

let opt f fmt = function
  | None -> Format.fprintf fmt "None"
  | Some x -> Format.fprintf fmt "Some(%a)" f x

let rec pp_list ?(sep = ";") pp_elt fmt = function
  | [h] -> Format.fprintf fmt "%a" pp_elt h
  | h :: t ->
      Format.fprintf fmt "%a%s@,%a" pp_elt h sep (pp_list ~sep pp_elt) t
  | [] -> ()

class debug_ast () =
  object (self)
    inherit Printer.extensible_printer ()

    method! term_node fmt t =
      match t.term_node with
      | TConst lc -> Format.fprintf fmt "TConst(%a)" self#logic_constant lc
      | TLval tl -> Format.fprintf fmt "TLVal(%a)" self#term_lval tl
      | TSizeOf ty -> Format.fprintf fmt "TSizeOf(%a)" (self#typ None) ty
      | TSizeOfE t -> Format.fprintf fmt "TSizeOfE(%a)" self#term t
      | TSizeOfStr s -> Format.fprintf fmt "TSizeOfStr(%s)" s
      | TAlignOf ty -> Format.fprintf fmt "TAlignOf(%a)" (self#typ None) ty
      | TAlignOfE t -> Format.fprintf fmt "TAlignOfE(%a)" self#term t
      | TUnOp (op, t) ->
          Format.fprintf fmt "TUnOp(%a,%a)" self#unop op self#term t
      | TBinOp (op, t1, t2) ->
          Format.fprintf fmt "TBinOp(%a,%a,%a)" self#binop op self#term t1
            self#term t2
      | TCastE (ty, t) ->
          Format.fprintf fmt "TCastE(%a,%a)" (self#typ None) ty self#term t
      | TAddrOf tl -> Format.fprintf fmt "TAddrOf(%a)" self#term_lval tl
      | TStartOf tl -> Format.fprintf fmt "TStartOf(%a)" self#term_lval tl
      | Tapp (li, ll, tl) ->
          Format.fprintf fmt "Tapp(%a,[%a],[%a])" self#logic_info li
            (pp_list self#logic_label) ll (pp_list self#term) tl
      | Tlambda (q, t) ->
          Format.fprintf fmt "Tlambda(%a,%a)" self#quantifiers q self#term t
      | TDataCons (_lci, tl) ->
          Format.fprintf fmt "TDataCons(_,[%a])" (pp_list self#term) tl
      | Tif (t1, t2, t3) ->
          Format.fprintf fmt "Tif(%a,%a,%a)" self#term t1 self#term t2
            self#term t3
      | Tat (t, l) ->
          Format.fprintf fmt "Tat(%a,%a)" self#term t self#logic_label l
      | Tbase_addr (l, t) ->
          Format.fprintf fmt "Tbase_addr(%a,%a)" self#logic_label l self#term t
      | Toffset (l, t) ->
          Format.fprintf fmt "Toffset(%a,%a)" self#logic_label l self#term t
      | Tblock_length (l, t) ->
          Format.fprintf fmt "Tblock_length(%a,%a)" self#logic_label l
            self#term t
      | Tnull -> Format.fprintf fmt "Tnull"
      | TLogic_coerce (ty, t) ->
          Format.fprintf fmt "TLogic_coerce(%a,%a)" (self#logic_type None) ty
            self#term t
      | TUpdate (t1, tof, t2) ->
          Format.fprintf fmt "TUpdate(%a,%a,%a)" self#term t1 self#term_offset
            tof self#term t2
      | Ttypeof t -> Format.fprintf fmt "Ttypeof(%a)" self#term t
      | Ttype ty -> Format.fprintf fmt "Ttype(%a)" (self#typ None) ty
      | Tempty_set -> Format.fprintf fmt "Tempty_set"
      | Tunion tl -> Format.fprintf fmt "Tunion[%a]" (pp_list self#term) tl
      | Tinter tl -> Format.fprintf fmt "Tinter[%a]" (pp_list self#term) tl
      | Tcomprehension (t, q, p) ->
          Format.fprintf fmt "Tcomprehension(%a,%a,Some(%a))" self#term t
            self#quantifiers q (opt self#predicate_named) p
      | Trange (t1, t2) ->
          Format.fprintf fmt "Trange(%a,%a)" (opt self#term) t1 (opt self#term)
            t2
      | Tlet (li, t) ->
          Format.fprintf fmt "Tlet(%a,%a)" self#logic_info li self#term t

    method! term_lval fmt (tl, o) =
      match tl with
      | TVar v ->
          Format.fprintf fmt "TVar(%a),%a" self#logic_var v self#term_offset o
      | TResult _ -> Format.fprintf fmt "TResult,%a" self#term_offset o
      | TMem t ->
          Format.fprintf fmt "TMem(%a),%a" self#term t self#term_offset o

    method! term_offset fmt =
      function
      | TNoOffset -> Format.fprintf fmt "TNoOffset"
      | TField (f, o) ->
          Format.fprintf fmt "TField(%a,%a)" self#fieldinfo f self#term_offset
            o
      | TModel (m, o) ->
          Format.fprintf fmt "TModel(%a,%a)" self#model_info m self#term_offset
            o
      | TIndex (t, o) ->
          Format.fprintf fmt "TIndex(%a,%a)" self#term t self#term_offset o

    method! predicate fmt p =
      match p.pred_content with
      | Pfalse -> Format.fprintf fmt "Pfalse"
      | Ptrue -> Format.fprintf fmt "Ptrue"
      | Papp (li, ll, tl) ->
          Format.fprintf fmt "Papp(%a,[%a],[%a])" self#logic_info li
            (pp_list self#logic_label) ll (pp_list self#term) tl
      | Pseparated tl ->
          Format.fprintf fmt "Pseparated(%a)" (pp_list self#term) tl
      | Prel (r, t1, t2) ->
          Format.fprintf fmt "Prel(%a,%a,%a)" self#relation r self#term t1
            self#term t2
      | Pand (p1, p2) ->
          Format.fprintf fmt "Pand(%a,%a)" self#predicate_named p1
            self#predicate_named p2
      | Por (p1, p2) ->
          Format.fprintf fmt "Por(%a,%a)" self#predicate_named p1
            self#predicate_named p2
      | Pxor (p1, p2) ->
          Format.fprintf fmt "Pxor(%a,%a)" self#predicate_named p1
            self#predicate_named p2
      | Pimplies (p1, p2) ->
          Format.fprintf fmt "Pimplies(%a,%a)" self#predicate_named p1
            self#predicate_named p2
      | Piff (p1, p2) ->
          Format.fprintf fmt "Piff(%a,%a)" self#predicate_named p1
            self#predicate_named p2
      | Pnot p -> Format.fprintf fmt "Pnot(%a)" self#predicate_named p
      | Pif (t, p1, p2) ->
          Format.fprintf fmt "Pif(%a,%a,%a)" self#term t self#predicate_named
            p1 self#predicate_named p2
      | Plet (li, p) ->
          Format.fprintf fmt "Plet(%a,%a)" self#logic_info li
            self#predicate_named p
      | Pforall (q, p) ->
          Format.fprintf fmt "Pforall(%a,%a)" self#quantifiers q
            self#predicate_named p
      | Pexists (q, p) ->
          Format.fprintf fmt "Pexists(%a,%a)" self#quantifiers q
            self#predicate_named p
      | Pat (p, l) ->
          Format.fprintf fmt "Pat(%a,%a)" self#predicate_named p
            self#logic_label l
      | Pvalid_read (l, t) ->
          Format.fprintf fmt "Pvalid_read(%a,%a)" self#logic_label l self#term
            t
      | Pvalid (l, t) ->
          Format.fprintf fmt "Pvalid(%a,%a)" self#logic_label l self#term t
      | Pvalid_function t ->
          Format.fprintf fmt "Pvalid_function(%a)" self#term t
      | Pinitialized (l, t) ->
          Format.fprintf fmt "Pinitialized(%a,%a)" self#logic_label l self#term
            t
      | Pdangling (l, t) ->
          Format.fprintf fmt "Pdangling(%a,%a)" self#logic_label l self#term t
      | Pallocable (l, t) ->
          Format.fprintf fmt "Pallocable(%a,%a)" self#logic_label l self#term t
      | Pfreeable (l, t) ->
          Format.fprintf fmt "Pfreeable(%a,%a)" self#logic_label l self#term t
      | Pfresh (l1, l2, t1, t2) ->
          Format.fprintf fmt "Pfresh(%a,%a,%a,%a)" self#logic_label l1
            self#logic_label l2 self#term t1 self#term t2

    method predicate_named = self#predicate
  end

let pp_term fmt t = (new debug_ast ())#term fmt t

let pp_toffset fmt t = (new debug_ast ())#term_offset fmt t

let pp_pred fmt p = (new debug_ast ())#predicate fmt p
