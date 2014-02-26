
/* run.config
OPT: -main nextSubset -stady -stady-msg-key generated-c,generated-pl -then -report
*/

/*@ predicate is_dset{L}(int *a, integer n) =
  @ \forall integer i; 0 <= i < n ==> (a[i] == 0 || a[i] == 1);
  @ predicate is_eq{L1,L2}(int *a, integer n) =
  @ \forall integer i; 0 <= i < n ==> \at(a[i],L1) == \at(a[i],L2);
  @ predicate lt{L1,L2}(int* a, integer i) =
  @ \at(a[i],L1) < \at(a[i],L2); */

/*@ requires n >= 0 && n <= 3 && \valid(s+(0..n-1)) && is_dset(s,n);
  @ assigns s[0..n-1];
  @ ensures is_dset(s,n);
  @ ensures -1 <= \result < n;
  @ ensures \result == -1 ==> is_eq{Pre,Post}(s,n);
  @ ensures \result != -1 ==> is_eq{Pre,Post}(s,\result);
  @ ensures \result != -1 ==> lt{Pre,Post}(s,\result);
  @*/
int nextSubset(int s[], int n) {
  int i,k;
  /*@ loop invariant -1 <= k <= n-1;
    @ loop assigns k;
    @ loop variant k; */
  for (k = n-1; k >= 0; k--) { if (s[k] == 0) { break; } }
  if (k == -1) { return -1; }
  s[k] = 1;
  /*@ loop invariant k+1 <= i <= n;
    @ loop invariant is_dset(s,i);
    @ loop assigns i,s[k+1..n-1];
    @ loop variant n-i; */
  for (i = k+1; i < n; i++) { s[i] = 0; }
  return k;
}
