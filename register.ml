
open Cil
open Cil_types
open Lexing



(* External functions *)

(*
let pc_run =
  let plugin = "PathCrawler" in
  let fname = "run_validate_asserts" in
  Dynamic.get ~plugin fname (Datatype.func Datatype.unit Datatype.unit)
*)





(* Available from the outside *)
module CounterExamples =
  State_builder.Hashtbl
    (Property.Hashtbl)
    (Datatype.Pair
       (Datatype.String) (* C testcase filename *)
       (Datatype.List
	  (Datatype.Pair
	     (*(Cil_datatype.Lval)*) (Datatype.String)
	     (*(Cil_datatype.Constant)*) (Datatype.String)
	  ))) (* entries *)
    (struct
      let name = "PCVA.CounterExamples"
      let dependencies = [Ast.self]
      let size = 64
     end)



(* outputs the AST of a project in a file *)
let print_in_file prj filename =
  Project.on prj (fun () ->
    let out = open_out filename in
    let fmt = Format.formatter_of_out_channel out in
    Printer.pp_file fmt (Ast.get());
    flush out;
    close_out out
  ) ()



let pc_emitter =
  Emitter.create "pcva" [Emitter.Property_status; Emitter.Funspec]
    ~correctness:[] ~tuning:[]



(* Fill the hashtable with pairs (location, property) of the AST *)
let fill_tbl tbl =
  (* puts (loc, property) of assertions in tbl *)
  Annotations.iter_all_code_annot (fun stmt _ ca ->
    let kf = Kernel_function.find_englobing_kf stmt in
    let ip = Property.ip_of_code_annot_single kf stmt ca in
    let loc = (fst (Cil_datatype.Stmt.loc stmt)).pos_lnum in
    Datatype.Int.Hashtbl.add tbl loc ip
  );
  Globals.Functions.iter (fun kf ->
    let vi = Kernel_function.get_vi kf in
    if not (is_builtin vi) then
	Annotations.iter_behaviors (fun _ beh ->
	(* puts (loc, property) of 'ensures' in tbl *)
	Annotations.iter_ensures (fun _emit (tk, cip) ->
	  let loc = (fst (cip.ip_loc)).pos_lnum in
	  let ip = Property.ip_of_ensures kf Kglobal beh (tk, cip) in
	  Datatype.Int.Hashtbl.add tbl loc ip
	) kf beh.b_name;
	(* puts (loc, property) of 'requires' in tbl *)
	Annotations.iter_requires (fun _ cip ->
	  let loc = (fst (cip.ip_loc)).pos_lnum in
	  let ip = Property.ip_of_requires kf Kglobal beh cip in
	  Datatype.Int.Hashtbl.add tbl loc ip
	) kf beh.b_name
      ) kf
  )




let print_list l name =
  let s = List.fold_left (fun x y -> Printf.sprintf "%s %3i" x y) "" l in
  Options.Self.debug ~level:1 "%s: %s" name s

(* Just add debug information to the 'Hashtbl.find' function *)
let find tbl tbl_name key =
  try Datatype.Int.Hashtbl.find tbl key
  with Not_found ->
    Options.Self.debug ~level:1 "Not_found: key %i in %s" key tbl_name;
    raise Not_found

let line = String.make 72 '-'
let print_break () =
  Options.Self.debug ~level:1 "%s" line






let run() =
  if Options.Enabled.get() then
    begin

      (* Map locs to properties *)
      let orig_tbl  = Datatype.Int.Hashtbl.create 32 in
      fill_tbl orig_tbl;


      (* We put the locs in lists *)
      let keys tbl ~no_repeat =
	let ret = ref [] in
	let f =
	  if no_repeat then
	    (fun k _ -> match !ret with
	    | i :: _ when i = k -> ()
	    | _ -> ret := k :: !ret)
	  else
	    (fun k _  -> ret := k :: !ret)
	in
	Datatype.Int.Hashtbl.iter_sorted f tbl;
	List.rev !ret
      in
      let l_orig = keys orig_tbl ~no_repeat:false in
      print_list l_orig "l_orig  ";
      
      CounterExamples.mark_as_computed()
    end





let extern_run () =
  Options.Enabled.set true;
  run ()
    

let extern_run = Dynamic.register ~plugin:"PCVA" ~journalize:true "run"
  (Datatype.func Datatype.unit Datatype.unit) extern_run


  
  
let run =
  let deps = [Ast.self; Options.Enabled.self] in
  let f, _self = State_builder.apply_once "pcva" deps run in
  f
    
let () = Db.Main.extend run
  
