
/* run.config
OPT: -main sum_array -stady -stady-msg-key generated-c -then -report
*/

/*@ requires n >= 0 && \valid(t+(0..n-1)) ;
  @ typically n <= 3;
  @ ensures \result == \sum(0,n-1,\lambda integer k; t[k]);
  @*/
double sum_array(double t[],int n) {
  int i;
  double s = 0;
  /*@ loop invariant 0 <= i <= n;
    @ loop invariant s == \sum(0,i-1,\lambda integer k; t[k]);
    @ loop variant n-i;
  */
  for(i=0; i < n; i++) s += t[i];
  return s;
}
