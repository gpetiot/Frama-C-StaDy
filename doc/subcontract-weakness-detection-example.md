# Example: Subcontract weakness detection

**Warning: this example is not up to date with StaDy v0.4.x**

Let us now consider a more complex program. The function all_zeros below returns a non-zero value if and only if, all the elements of the array t of size n are non-zero.

      

	/*@ requires n>=0 && \valid(t+(0..n-1));
            assigns \nothing ;
            ensures \result != 0 <==>
		    ( \forall integer j; 0 <= j < n ==> t[j] == 0);
	*/
	int all_zeros(int t[], int n) {
          int k;
          /*@ loop invariant 0 <= k <= n;
              loop assigns k;
              loop variant n-k;
          */
          for (k = 0; k < n; k++)
            if (t[k] != 0)
              return 0;
            return 1;
        }
      

    

The deductive verification of the program by the Wp plug-in of Frama-C does not succeed: the postcondition of the function all_zeros is not verified.

      [wp] Running WP plugin...
      [wp] Collecting axiomatic usage
      [wp] warning: Missing RTE guards
      [wp] 10 goals scheduled
      [wp] [Qed] Goal typed_all_zeros_loop_inv_established : Valid
      [wp] [Qed] Goal typed_all_zeros_loop_assign : Valid
      [wp] [Qed] Goal typed_all_zeros_assign_part1 : Valid
      [wp] [Qed] Goal typed_all_zeros_assign_part2 : Valid
      [wp] [Qed] Goal typed_all_zeros_assign_part3 : Valid (1ms)
      [wp] [Qed] Goal typed_all_zeros_assign_part4 : Valid (1ms)
      [wp] [Qed] Goal typed_all_zeros_loop_term_decrease : Valid (1ms)
      [wp] [Qed] Goal typed_all_zeros_loop_term_positive : Valid (1ms)
      [wp] [Alt-Ergo] Goal typed_all_zeros_loop_inv_preserved : Valid (Qed:1ms) (44ms) (17)
      [wp] [Alt-Ergo] Goal typed_all_zeros_post : Unknown (Qed:2ms) (507ms)
      [wp] Proved goals: 9 / 10
      Qed:      8 (0ms-1ms)
      Alt-Ergo: 1 (44ms-44ms) (17) (unknown: 1)
    

We can apply StaDy to look for a non-compliance between the code and its specification.

      frama-c all_zeros.c -main all_zeros -stady -stady-stop-when-assert-violated -stady-timeout 5
    

      [stady] all-paths: true
      [stady] 19246 test cases
    

StaDy did not exhibit any counterexample of non-compliance. An enlightened user may get the feeling that the program is correct but insufficiently specified. We re-apply StaDy to look for counterexamples exhibiting subcontract weaknesses:

      frama-c all_zeros.c -main all_zeros -stady -stady-swd 2 -stady-stop-when-assert-violated
    

Here, 2 is the identifier of the loop and its contract, it is retrieved by clicking on the beginning of the while loop in the GUI of Frama-C.

      [stady] all-paths: true
      [stady] 57 test cases
      [stady] Subcontract Weakness of stmt 2 for ensures
      \result != 0 <==>
	(\forall integer j;
	0 <= j < \old(n) ==> *(\old(t)+j) == 0)
      LOCATION: all_zeros_unproved_1.c:12
      TEST DRIVER: testcases___[...]/all_zeros/testdrivers/TC_9.c
      n = 1
      nondet_sint_val[0] = 1
      return value = -- OUTPUT: 1 (1)
      t[0] = 6432
    

This output means that the loop contract (stmt 2) is not strong enough for the postcondition of the function. The counterexample has to be read as follows:

    we consider as inputs: n = 1, t[0] = 6432
    we replace the execution of the loop by the most general code satisfying its loop contract, that is:
        only k can be modified
        the new value of k has to satisfy 0 <= k <= n
    a non-deterministic value is thus assigned to k: k = 1 (designated by nondet_sint_val[0] in the feedback of StaDy)

However, this new code for the loop does not change the return value of the function to 0 when one of the element is non-zero, so the new function always returns 1 (OUTPUT: 1 in the feedback of StaDy). We now realize that we might need a loop invariant over the values of the array elements. We add such a loop invariant (highlighted in yellow):

      

	/*@ requires n>=0 && \valid(t+(0..n-1));
            assigns \nothing;
            ensures \result != 0 <==>
               ( \forall integer j; 0 <= j < n ==> t[j] == 0);
        */
        int all_zeros(int t[], int n) {
          int k;
          /*@ loop invariant 0 <= k <= n;
              loop invariant \forall integer j; 0<=j<k ==> t[j]==0;
              loop assigns k;
              loop variant n-k;
	  */
          for (k = 0; k < n; k++)
            if (t[k] != 0)
              return 0;
          return 1;
        }
      

    

With this new loop invariant, StaDy does not exhibit any counterexample of contract weakness:

      frama-c all_zeros.c -main all_zeros -stady -stady-swd 2 -stady-timeout 5 -stady-stop-when-assert-violated
    

      [stady] all-paths: true
      [stady] 30002 test cases
    

And the program can now be formally verified with Wp:

      [wp] Running WP plugin...
      [wp] Collecting axiomatic usage
      [wp] warning: Missing RTE guards
      [wp] 12 goals scheduled
      [wp] [Qed] Goal typed_all_zeros_loop_inv_established : Valid
      [wp] [Qed] Goal typed_all_zeros_loop_inv_2_established : Valid
      [wp] [Qed] Goal typed_all_zeros_loop_assign : Valid
      [wp] [Alt-Ergo] Goal typed_all_zeros_loop_inv_2_preserved : Valid (Qed:1ms) (23ms) (24)
      [wp] [Alt-Ergo] Goal typed_all_zeros_loop_inv_preserved : Valid (Qed:1ms) (29ms) (17)
      [wp] [Alt-Ergo] Goal typed_all_zeros_post : Valid (Qed:3ms) (37ms) (54)
      [wp] [Qed] Goal typed_all_zeros_assign_part1 : Valid
      [wp] [Qed] Goal typed_all_zeros_assign_part2 : Valid	
      [wp] [Qed] Goal typed_all_zeros_assign_part3 : Valid (1ms)
      [wp] [Qed] Goal typed_all_zeros_assign_part4 : Valid
      [wp] [Qed] Goal typed_all_zeros_loop_term_decrease : Valid (1ms)
      [wp] [Qed] Goal typed_all_zeros_loop_term_positive : Valid (1ms)
      [wp] Proved goals: 12 / 12
      Qed:      9 (0ms-3ms)
      Alt-Ergo: 3 (23ms-37ms) (54)

