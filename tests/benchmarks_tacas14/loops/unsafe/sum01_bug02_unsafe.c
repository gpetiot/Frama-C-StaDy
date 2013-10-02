
#define a (2)

void f(unsigned int n) { 
  int i, j=10, sn=0;
  for(i=1; i<=n; i++) {
    if (i<j) 
    sn = sn + a;
    j--;
  }
  //@ assert(sn==n*a || sn == 0);
}
