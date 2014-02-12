
/* run.config
OPT: -main firstSubset -stady -then -report
*/

/* @ predicate is_dset{L}(int *a, integer n) =
      \forall integer i; 0 <= i < n ==> (a[i] == 0 || a[i] == 1); */

/*@ requires n >= 0 && n <= 3 && \valid(s+(0..n-1));
  @ assigns s[0..n-1];
  @ ensures \forall integer i; 0 <= i < n ==> (s[i] == 0 || s[i] == 1); */
void firstSubset(int s[], int n) {
 int k;
 /*@ loop invariant 0 <= k <= n;
   @ loop invariant \forall integer i; 0 <= i < k ==> (s[i] == 0 || s[i] == 1);
   @ loop assigns k, s[0..n-1];
   @ loop variant n-k; */
 for ( k = 0; k < n; k++) {
  s[k] = 0;
 }
}
