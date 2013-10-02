
#define a (2)

/*@ requires 0 < n < 20; */
void f(unsigned int n) { 
  int i, sn=0;
  for(i=1; i<=n; i++) {
    if (i<10)
      sn = sn + a;
  }
  //@ assert(sn==n*a || sn == 0);
}
