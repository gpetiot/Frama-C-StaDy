
#define a (2)
#define SIZE 8

void f() { 
  int i, sn=0;
  for(i=1; i<=SIZE; i++) {
    if (i<4)
    sn = sn + a;
  }
  //@ assert(sn==SIZE*a || sn == 0);
}

