
/* run.config
STDOPT: +"-main f -stady -stady-cwd 3 -stady-msg-key generated-c,generated-pl -stady-stop-when-assert-violated -then -report"
*/

int found;

/*@ requires \valid(t+(0..4));
  @*/
void f(int*t, int x) {
  int i;
  found = 0;

  /*@ loop invariant 0 <= i <= 5;
    @ //loop invariant found <==> (\exists integer k; 0 <= k < i && t[k] == x);
    @ loop assigns found, i;
    @*/
  for(i = 0; i <= 4; i++) {
    if(t[i] == x)
      found = 1;
  }

  //@ assert found <==> \exists integer i; 0 <= i <= 4 && t[i] == x;
}

