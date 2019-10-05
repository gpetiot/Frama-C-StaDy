include Plugin.S

module Enabled : Parameter_sig.Bool

module Version : Parameter_sig.Bool

module PathCrawler_Options : Parameter_sig.String

module Socket_Type : Parameter_sig.String

module Timeout : Parameter_sig.Int

module Stop_When_Assert_Violated : Parameter_sig.Bool

module Precondition : Parameter_sig.String

module Replace_Functions : Parameter_sig.String

(* Property selection *)
module Functions : Parameter_sig.String_list

module Behaviors : Parameter_sig.String_list

module Properties : Parameter_sig.String_list

(* Testing subcontracts *)
module SWD : Parameter_sig.String_list

module Simulate_Functions : Parameter_sig.String_list

(* Debug Keys *)
val dkey_input_domain : category

val dkey_generated_pl : category

val dkey_socket : category

val dkey_generated_c : category

val dkey_insertions : category
