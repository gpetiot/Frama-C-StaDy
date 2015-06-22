
let () = Plugin.is_share_visible ()

module Self = Plugin.Register (struct
  let name = "StaDy"
  let shortname = "stady"
  let help = "Counter-Example Generation by Dynamic Analysis"
end)
  
module Enabled = Self.False (struct
  let option_name = "-stady"
  let help = ""
end)

module PathCrawler_Options = Self.String (struct
  let option_name = "-stady-pc-options"
  let help = "command line options for PathCrawler"
  let arg_name = "options"
  let default = ""
end)

module Socket_Type = Self.String (struct
  let option_name = "-stady-socket"
  let help = "use internet socket or unix socket or standard i/o"
  let arg_name = "internet | unix | stdio"
  let default = "internet"
end)

let () = Socket_Type.set_possible_values ["internet"; "unix"; "stdio"]

module Functions = Self.String_list (struct
  let option_name = "-stady-fct"
  let arg_name = "f,..."
  let help = ""
end)

module Behaviors = Self.String_list (struct
  let option_name = "-stady-bhv"
  let arg_name = "b,..."
  let help = ""
end)

module Properties = Self.String_list (struct
  let option_name = "-stady-prop"
  let arg_name = "p,..."
  let help = ""
end)

module SWD = Self.String_list (struct
  let option_name = "-stady-swd"
  let help = "detect contract weaknesses"
  let arg_name = "i,..."
end)

module Simulate_Functions =
  Self.String_list
    (struct
      let option_name = "-stady-sim-fct"
      let arg_name = "f,..."
      let help = "simulate a function execution based on its postcondition"
    end)

module Timeout =
  Self.Int
    (struct
      let option_name = "-stady-timeout"
      let help = "timeout for the test generator (in seconds), \
		  no timeout if n <= 0 (default: no timeout)"
      let arg_name = "n"
      let default = 0
    end)

module Stop_When_Assert_Violated =
  Self.False
    (struct
      let option_name = "-stady-stop-when-assert-violated"
      let help = "stop the test generation at the first violated assertion"
    end)

(* Debug Keys *)

let dkey_native_precond = Self.register_category "native-precond"
let dkey_generated_pl = Self.register_category "generated-pl"
let dkey_socket = Self.register_category "socket"
let dkey_generated_c = Self.register_category "generated-c"
let dkey_insertions = Self.register_category "insertions"
