
//x is an input variable
int x = 0;

void foo() {
  x--;
}

/*@ requires \valid(T+(0..nondet_x-1));
  @ requires nondet_x <= 11;
  @*/
void f(int nondet_x, int* T) {
  int i = 0;
  x = nondet_x;
  while (x > 0) {
    int c = T[i++];
    if(c) foo();
    else foo();
  }
  //@ assert(x==0);
}



