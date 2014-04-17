
/* run.config
OPT: -main merge_arrays -stady -stady-msg-key generated-c,generated-pl -then -report
*/

/*@ requires 0 <= l1;
  @ requires 0 <= l2;
  @ requires \valid_read(t1+(0..l1-1));
  @ requires \valid_read(t2+(0..l2-1));
  @ requires \valid(t3+(0..(l1+l2-1)));
  @ requires \forall int i; 0 <= i < l1-1 ==> t1[i] <= t1[i+1];
  @ requires \forall int i; 0 <= i < l2-1 ==> t2[i] <= t2[i+1];
  @ typically l1 <= 3;
  @ typically l2 <= 3;
  @ ensures \forall int i; 0 <= i < l1+l2-1 ==> t3[i] <= t3[i+1];
  @*/
void merge_arrays (int t1[], int t2[], int t3[], int l1, int l2) {
  int i = 0, j = 0, k = 0;

  /*@ loop invariant 0 <= i <= l1;
    @ loop invariant 0 <= j <= l2;
    @ loop invariant 0 <= k <= l1+l2;
    @ loop invariant k == i+j;
    @ loop variant l1+l2-k;
    @*/
  while (i < l1 && j < l2) {
    if (t1[i] < t2[j]) {
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
      loop variant l1-i;
  */
  while (i < l1) {
    t3[k] = t1[i];
    i++;
    k++;
  }
  /*@ loop invariant 0 <= j <= l2;
      loop invariant 0 <= k <= l1+l2;
      loop invariant k == i+j;
      loop variant l2-j;
  */
  while (j < l2) {
    t3[k] = t2[j];
    j++;
    k++;
  }
}
