
/* run.config
STDOPT: +"-main f -stady -stady-rpl-fct Count/count -stady-msg-key generated-c,generated-pl -then -report"
*/

/*@
axiomatic CountAxiomatic {
  logic int Count{L}(int* a, int n, int v) 
    reads a[0 .. n - 1];
  }

*/

int count (int* a, int n, int v) {
  int r = 0;
  int i;
  for (i = 0; i < n; i++)
    if (a[i] == v)
      r++;
  return r;
}

/*@
  requires 1 <= n <= 5;
  requires \valid(a+(0..n-1));
  ensures Count(a, n, (int)4) == n;
*/
void f(int* a, int n, int v) {
  int i;
  for (i = 0; i < n; i++)
    a[i] = 4;
}
