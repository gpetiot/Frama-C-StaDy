

//x is an input variable
int x;

void foo() {
  x--;
}


/*@ requires \valid(nondet_bool+(0..100));
  @ requires -100 <= nondet_x <= 100;
  @*/
void f(int nondet_x, _Bool* nondet_bool) {
  int i = 0;
  x = nondet_x;
  /*@ loop invariant 0 <= i;
    @*/
  while (x > 0) {
    _Bool c = nondet_bool[i++];
    if(c) foo();
    else foo();
  }
  //@ assert(x<=0);
}



