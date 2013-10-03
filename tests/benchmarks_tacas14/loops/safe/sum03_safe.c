
#define a (2)

void f(unsigned int loop1, unsigned int n1) { 
  int sn=0;
  unsigned int x=0;

  /*@ loop invariant sn == x*a;
    @*/
  while(1){
    if(x == 100) break;
    sn = sn + a;
    x++;
    //@ assert(sn==x*a || sn == 0);
  }
}

