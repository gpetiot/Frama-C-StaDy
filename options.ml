

module Self = Plugin.Register (struct
  let name = "pcva"
  let shortname = "pcva"
  let help = ""
end)
  
module Enabled = Self.False (struct
  let option_name = "-pcva"
  let help = ""
end)

module Temp_File = Self.String (struct
  let option_name = "-pcva-temp-file"
  let help = ""
  let arg_name = "file_name"
  let default = "pcva_temp.c"
end)

module PathCrawler_Options = Self.String (struct
  let option_name = "-pcva-pc-options"
  let help = "command line options for PathCrawler"
  let arg_name = "options"
  let default = ""
end)
