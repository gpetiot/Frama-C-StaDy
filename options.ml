

module Self = Plugin.Register (struct
  let name = "PCVA"
  let shortname = "pcva"
  let help = ""
end)
  
module Enabled = Self.False (struct
  let option_name = "-pcva"
  let help = ""
end)
