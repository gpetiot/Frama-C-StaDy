
#define a (2)

/*@ requires n < 10;
  @*/
void f(unsigned int n) { 
  int i, sn=0;
  for(i=1; i<=n; i++) {
    sn = sn + a;
    if (i==4) sn=-10;
  }
  //@ assert(sn==n*a || sn == 0);
}
