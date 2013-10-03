
/*@ requires n <= 100;
  @*/
void f(unsigned int n) { 
  unsigned int i, sn=0;

  /*@ loop invariant 0 <= i <= n+1;
    @ loop invariant sn == i*(i-1)/2;
    @ loop variant n+1-i;
    @*/
  for(i=0; i<=n; i++) {
    sn = sn + i;
  }
  //@ assert(sn==(n*(n+1))/2 || sn == 0);
}
