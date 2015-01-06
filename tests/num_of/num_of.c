
/* run.config
STDOPT: +"-main num_of -stady -stady-msg-key generated-c,generated-pl -then -report"
*/

/*@ requires n > 0;
  @ requires \valid(t+(0..n-1));
  @ typically n <= 3;
  @ assigns \nothing;
  @ ensures \result == \numof(0, n-1, \lambda integer k; t[k] == 0);
  @*/
int num_of (int n, int* t) {
  int num = 0;
  int i;
  /*@ loop invariant 0 <= num <= i <= n;
    @ loop invariant num == \numof(0, i-1, \lambda integer k; t[k] == 0);
    @ loop assigns num, i;
    @ loop variant n-i;
    @*/
  for(i = 0; i < n; i++)
    if(t[i] == 0)
      num ++;
  return num;
}
