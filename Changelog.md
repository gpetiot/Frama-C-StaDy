
v0.4.3 	11/03/2018 new option -stady-rpl-fct to replace ACSL logic functions
                   with C functions

v0.4.2 	04/03/2018 fix #3, #4 (issues on structures)

v0.4.1
	08/01/2018 put brackets around code generated before a stmt,
	           and around code generated after a stmt, always put
	           brackets around if/else instructions
v0.4.0
	17/12/2017 Frama-C Sulfur compliant

v0.3.0
	17/12/2017 Frama-C Phosphorus compliant

v0.2.3
	08/10/2017 fix translation of unary minus operator

v0.2.2
	08/03/2017 add missing mpz_clear calls in translation

v0.2.1
	18/02/2017 new option -stady-version

v0.2.0
	18/02/2017 -stady-swd now takes labels instead of stmt ids
	16/02/2017 fix SWD translation (loop invariant when there is
				no loop iteration)
	15/02/2017 new option -stady-precondition to add a 'typically'
				precondition

v0.1.0 	undocumented
