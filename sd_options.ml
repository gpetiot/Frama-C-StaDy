
let () = Plugin.is_share_visible ()

module Self = Plugin.Register (struct
  let name = "StaDy"
  let shortname = "stady"
  let help = ""
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

module Behavior_Reachability = Self.False (struct
  let option_name = "-stady-bhv-reach"
  let help = "compute reachability of each function's behavior"
end)

module Spec_Insuf = Self.Int (struct
  let option_name = "-stady-spec-insuf"
  let help = "replace a loop or function call by its specification"
  let arg_name = "i"
  let default = -500
end)

module Simulate_Functions =
  Self.String_list
    (struct
      let option_name = "-stady-sim-fct"
      let arg_name = "f,..."
      let help = "simulate a function execution based on its postcondition"
    end)


(* Debug Keys *)

let dkey_native_precond = Self.register_category "native-precond"
let dkey_generated_pl = Self.register_category "generated-pl"
let dkey_socket = Self.register_category "socket"
let dkey_generated_c = Self.register_category "generated-c"
let dkey_properties = Self.register_category "properties"
let dkey_reach = Self.register_category "reach"
let dkey_insertions = Self.register_category "insertions"

(* mpz_t type for GMP *)
let mpz_t = ref (None:Cil_types.typ option)
