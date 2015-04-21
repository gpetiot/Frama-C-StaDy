
open Cil_types

let ref_cwd = ref ([] : int list)

let reset_cwd () = ref_cwd := []

let print_cwd () =
  let pp_int fmt x = Format.fprintf fmt "%i" x in
  let pp_int_list = Pretty_utils.pp_list ~sep:"," pp_int in
  Options.Self.debug ~level:1 "cwd: %a@." pp_int_list !ref_cwd

let add_cwd sid =
  ref_cwd := sid :: !ref_cwd;
  print_cwd()

let rem_cwd sid =
  ref_cwd := List.filter (fun x-> x <> sid) !ref_cwd;
  print_cwd()


let pc_panel
      (compute: ?props:Property.t list -> ?cwd:int list -> unit -> unit)
      (main_ui:Design.main_window_extension_points) =
  let vbox = GPack.vbox () in
  let packing = vbox#pack ~expand:true ~fill:true in
  let w = GPack.table ~packing ~columns:2 () in
  let box_4 = GPack.hbox ~packing:(w#attach ~left:1 ~top:4) () in
  let tooltip = "Entry point" in
  let validator s = List.mem s (Kernel.MainFunction.get_possible_values ()) in
  let get = Kernel.MainFunction.get in
  let set = Kernel.MainFunction.set in
  let refresh = Gtk_helper.on_string ~tooltip ~validator box_4 "main" get set in
  let run_button = GButton.button ~label:"Run" ~packing:(vbox#pack) () in
  let callback() = compute ~cwd:(!ref_cwd) (); main_ui#redisplay() in
  let on_press() = main_ui#protect ~cancelable:true callback in
  ignore(run_button#connect#pressed on_press);
  "stady", vbox#coerce, Some refresh


let to_do_on_select
      (popup_factory:GMenu.menu GMenu.factory)
      (main_ui:Design.main_window_extension_points) button_nb selected
      (compute: ?props:Property.t list -> ?cwd:int list -> unit -> unit) =
  match selected with
  | Pretty_source.PStmt(_,({skind=Loop _} as stmt))
  | Pretty_source.PStmt(_,({skind=Instr(Call _)} as stmt)) when button_nb = 3 ->
     let callback() = add_cwd stmt.sid in
     let str1 = "Add this contract to the CWD list" in
     ignore (popup_factory#add_item str1 ~callback);
     let callback() = rem_cwd stmt.sid in
     let str2 = "Remove this contract from the CWD list" in
     ignore (popup_factory#add_item str2 ~callback)
  | Pretty_source.PIP prop when button_nb = 1 ->
     main_ui#pretty_information "%a" Utils.pp_ce prop
  | Pretty_source.PIP prop when button_nb = 3 ->
     begin
       try
	 let nc_tbl = States.NC_counter_examples.find prop in
	 let on_file tc_c _ =
	   let callback() =
	     let prj = Project.create tc_c in
	     let s = State_selection.of_list[Kernel.PreprocessAnnot.self] in
	     Project.copy ~selection:s prj;
	     Project.on prj File.init_from_c_files [File.from_filename tc_c]
	   in
	   let item_str = Printf.sprintf "_Open %s in new project" tc_c in
	   ignore (popup_factory#add_item item_str ~callback)
	 in
	 Datatype.String.Hashtbl.iter_sorted on_file nc_tbl
       with Not_found -> ()
     end;
     let callback() = compute ~props:[prop] (); main_ui#redisplay() in
     ignore(popup_factory#add_item "Validate property with StaDy" ~callback)
  | _ -> ()


let pc_selector
      compute menu (main_ui:Design.main_window_extension_points) ~button loc =
  to_do_on_select menu main_ui button loc compute


let main main_ui =
  try
    Register.setup_props_bijection();
    Register.do_externals();
    let compute = Register.compute_props in
    main_ui#register_panel (pc_panel compute);
    main_ui#register_source_selector (pc_selector compute)
  with _ -> ()


let () =
  Design.register_extension main;
  Design.register_reset_extension
    (fun main -> main#protect ~cancelable:false reset_cwd)
