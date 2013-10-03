
#define a (2)
#define SIZE 8


void f() { 
  int i, sn=0;

  /*@ loop invariant 1 <= i <= SIZE+1;
    @ loop invariant sn == (i-1)*a;
    @ loop variant SIZE+1-i;
    @*/
  for(i=1; i<=SIZE; i++) {
    sn = sn + a;
  }
  //@ assert(sn==SIZE*a || sn == 0);
}

