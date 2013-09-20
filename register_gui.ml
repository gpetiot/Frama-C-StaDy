
open Cil_types
open Pretty_source 



let pc_panel (main_ui:Design.main_window_extension_points) =
  let vbox = GPack.vbox () in
  let packing = vbox#pack ~expand:true ~fill:true in
  let w = GPack.table ~packing ~columns:2 () in
  let box_4 = GPack.hbox ~packing:(w#attach ~left:1 ~top:4) () in
  let tooltip =
    Pretty_utils.sfprintf "%s" Kernel.MainFunction.parameter.Parameter.help in
  let validator s = List.mem s (Kernel.MainFunction.get_possible_values ()) in
  let refresh =
    Gtk_helper.on_string ~tooltip ~validator
      box_4 "main" Kernel.MainFunction.get Kernel.MainFunction.set in
  let run_button = GButton.button ~label:"Run" ~packing:(vbox#pack) () in
  let _ = run_button#connect#pressed
    (fun () -> main_ui#protect ~cancelable:true
      (fun () -> Register.run(); main_ui#redisplay())) in
  "pcva", vbox#coerce, Some refresh
  


let to_do_on_select
    (popup_factory:GMenu.menu GMenu.factory)
    (main_ui:Design.main_window_extension_points) button_nb selected =
  match selected with
  | PIP prop ->
    begin
      try
	let tc_c, l = Register.TestFailures.find prop in
	if button_nb = 1 then
	    begin
	      main_ui#pretty_information
		"Counter-example (by PathCrawler-VA):@.";
	      List.iter (fun (s,v) ->
		main_ui#pretty_information "%s = %s@." s v) l;
	      if tc_c <> "" then
		main_ui#pretty_information "@\ntestcase file: %s@." tc_c
	    end
	  else if button_nb = 3 then
	    let open_testcase () =
	      let prj = Project.create tc_c in
	      Project.copy ~selection:(State_selection.of_list
	      [Kernel.PreprocessAnnot.self]) prj;
	      Project.on prj (fun () ->
		File.init_from_c_files [File.from_filename tc_c];
		!Db.RteGen.compute()
	      ) () in
	    if tc_c <> "" then
	      ignore
		(popup_factory#add_item
		   "_Open counter-example in new project"
                   ~callback:open_testcase)
      with
      | _ -> ()
    end
  | _ -> ()


let pc_selector
    menu (main_ui:Design.main_window_extension_points) ~button localizable =
  to_do_on_select menu main_ui button localizable


let main main_ui =
  (*Options.Enabled.set true;*)
  main_ui#register_panel pc_panel;
  main_ui#register_source_selector pc_selector

let () =
  Design.register_extension main
