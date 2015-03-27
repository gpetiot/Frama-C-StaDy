/* run.config
STDOPT: +"-main f -stady -stady-msg-key generated-c,generated-pl -stady-cwd 9 -stady-stop-when-assert-violated -then -report"
*/

int fmax(int x, int y) {
  return (x >= y) ? x : y;
}

/*@
    requires n >= 3;
    requires \valid(t+(0..n-1));
    typically n < 6;
    assigns t[2..n-1];
*/
void f(int n, int * t) {
  int i = 3;

  t[2] = fmax(t[1], t[0]);

  /*@
      loop invariant 3 <= i <= n;
      loop invariant \forall integer k; 2 <= k < i-1 ==>
                 (t[k] == t[k-1] || t[k] == t[k-2]);
      loop assigns i, t[3..n-1];
      loop variant n-i;
  */
  while(i<n) {
    t[i] = fmax(t[i-1], t[i-2]);
    i++;
  }
}
