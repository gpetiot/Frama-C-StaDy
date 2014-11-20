/* run.config
OPT: -main f -stady -stady-msg-key generated-c,generated-pl -then -report
*/

struct S {
  int s_i;
};

//@ type invariant inv_int(int x) = 0 <= x;
//@ type invariant inv_s(struct S x) = x.s_i % 2 == 0;

/*@ requires x > 100;
  @ requires x == 2*y;
  @*/
void f(int x, int y) {
  struct S s;
  s.s_i = x;
}
