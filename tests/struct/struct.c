
/* run.config
STDOPT: +"-main f -stady -stady-msg-key generated-c,generated-pl -then -report"
*/

struct S {
  int i;
  int *p;
};

/*@ requires \valid(s);
  @ requires 0 <= n <= 5;
  @ requires 0 <= s->i <= 10;
  @ requires \valid(s->p);
  @ requires \valid(s2);
  @ requires \valid((s2->p)+(0..9));
  @*/
int f(struct S* s, struct S* s2, int n) {
  if(s->i)
    return 1;
  else
    return -1;
}
