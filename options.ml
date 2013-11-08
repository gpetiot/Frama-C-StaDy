

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
