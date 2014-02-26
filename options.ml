

module Self = Plugin.Register (struct
  let name = "StaDyPlus"
  let shortname = "stady"
  let help = ""
end)
  
module Enabled = Self.False (struct
  let option_name = "-stady"
  let help = ""
end)

module Temp_File = Self.String (struct
  let option_name = "-stady-temp-file"
  let help = ""
  let arg_name = "file_name"
  let default = "stady_temp.c"
end)

module Precond_File = Self.String (struct
  let option_name = "-stady-precond-file"
  let help = ""
  let arg_name = "file_name"
  let default = "stady_precond.pl"
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

module Functions = Self.StringList (struct
  let option_name = "-stady-fct"
  let arg_name = "f,..."
  let help = ""
end)

module Behaviors = Self.StringList (struct
  let option_name = "-stady-bhv"
  let arg_name = "b,..."
  let help = ""
end)

module Properties = Self.StringList (struct
  let option_name = "-stady-prop"
  let arg_name = "p,..."
  let help = ""
end)


(* Debug Keys *)

let dkey_native_precond = Self.register_category "native-precond"
let dkey_generated_pl = Self.register_category "generated-pl"
let dkey_socket = Self.register_category "socket"
let dkey_lengths = Self.register_category "lengths"
let dkey_at = Self.register_category "at"
let dkey_second_pass = Self.register_category "second-pass"
let dkey_generated_c = Self.register_category "generated-c"
let dkey_properties = Self.register_category "properties"
