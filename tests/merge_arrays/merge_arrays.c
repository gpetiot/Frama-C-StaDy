/* run.config
   OPT: -pc -pc-test-params="tests/Merge/test_parameters_Merge.pl" -pc-share $(pwd)/tests/.share -pc-trace -pc-tests -kernel-debug 0 -verbose 0 -pc-deter -pc-trace-preconds -pc-trace-simpred -pc-trace-result -pc-k-path 2 -main Merge
*/




/*@ requires 0 <= l1 <= 3;
  @ requires 0 <= l2 <= 3;
  @ requires \block_length(t1) == l1*sizeof(int);
  @ requires \block_length(t2) == l2*sizeof(int);
  @ requires \block_length(t3) == (l1+l2)*sizeof(int);
  @ requires \forall int i; 0 <= i < l1-1 ==> t1[i] <= t1[i+1];
  @ requires \forall int i; 0 <= i < l2-1 ==> t2[i] <= t2[i+1];
  @ ensures \forall int i; 0 <= i < l1+l2-1 ==> t3[i] <= t3[i+1];
  @*/
void Merge (int t1[], int t2[], int t3[], int l1, int l2) {
  int i = 0;
  int j = 0;
  int k = 0;

  while (i < l1 && j < l2) {     /* line 21 */
    if (t1[i] < t2[j]) {     /* line 22 */
      t3[k] = t1[i];
      i++;
    }
    else {
      t3[k] = t2[j];
      j++;
    }
    k++;
  }
  /*@ loop invariant 0 <= i <= l1;
      loop invariant 0 <= k <= l1+l2;
      loop invariant k == i+j;
      loop variant l1-j;
  */
  while (i < l1) {     /* line 32 */
    t3[k] = t1[i];
    i++;
    k++;
  }
  /*@ loop invariant 0 <= j <= l2;
      loop invariant 0 <= k <= l1+l2;
      loop invariant k == i+j;
      loop variant l2-j;
  */
  while (j < l2) {     /* line 37 */
    t3[k] = t2[j];
    j++;
    k++;
  }
}
