
#define a (2)


void f(int n) { 
  int i, sn=0;
  /*@ loop invariant sn == a*(i-1) || sn == 0;
    @ loop invariant 1 <= i <= n+1;
    @ loop variant n*a - sn;
    @*/
  for(i=1; i<=n; i++) {
    sn = sn + a;
  }
  //@ assert(sn==n*a || sn == 0);
}
