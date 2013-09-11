

module Self = Plugin.Register (struct
  let name = "pcva"
  let shortname = "pcva"
  let help = ""
end)
  
module Enabled = Self.False (struct
  let option_name = "-pcva"
  let help = ""
end)
