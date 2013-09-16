
open Cil
open Cil_types
open Lexing

 



(* outputs the AST of a project in a file *)
let print_in_file prj filename =
  Project.on prj (fun () ->
    (* first pass: prepare the quantifiers predicates, ignore the output *)
    let fmt = Format.make_formatter (fun _ _ _ -> ()) ignore in
    Pcva_printer.First_pass.pp_file fmt (Ast.get());

    (* second pass: print the instrumented quantif, output in a file *)
    let out = open_out filename in
    let fmt = Format.formatter_of_out_channel out in
    Pcva_printer.Second_pass.pp_file fmt (Ast.get());
    flush out;
    close_out out
  ) ()





let run() =
  if Options.Enabled.get() then
    begin
      (* Settings *)
      Kernel.Unicode.set false;

      (* Bijection :
	 unique_identifier <--> property
      *)
      let property_id = ref 0 in
      Property_status.iter (fun property ->
	let pos1,_ = Property.location property in
	let fc_builtin = "__fc_builtin_for_normalization.i" in
	if (Filename.basename pos1.pos_fname) <> fc_builtin then
	  begin
	    Datatype.Int.Hashtbl.add
	      Prop_id.id_to_prop_tbl !property_id property;
	    Property.Hashtbl.add Prop_id.prop_to_id_tbl property !property_id;
	    property_id := !property_id + 1
	  end
      );

      Datatype.Int.Hashtbl.iter (fun prop_id prop ->
	Options.Self.debug ~level:1 "loc: %a (id: %i)" 
	  Printer.pp_location (Property.location prop) prop_id
      ) Prop_id.id_to_prop_tbl;



      (* Save the result in a file *)
      print_in_file (Project.current()) (Options.Temp_File.get());


      let cmd =
	Printf.sprintf "frama-c %s -main %s -pc %s"
	  (Options.Temp_File.get())
	  (Kernel_function.get_name (fst(Globals.entry_point())))
	  (Options.PathCrawler_Options.get())
      in
      let ret = Sys.command cmd in
      Options.Self.feedback "code retour: %i" ret

    end






  
  
let run =
  let deps = [Ast.self; Options.Enabled.self] in
  let f, _self = State_builder.apply_once "pcva" deps run in
  f
    
let () = Db.Main.extend run
  
