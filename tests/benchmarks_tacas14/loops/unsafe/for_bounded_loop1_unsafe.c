

/*@ requires 0 < n < 10;
  @ requires \valid(non_det_y+(0..n-1));
  @ requires \forall int i; 0 <= i < n ==> non_det_y[i] != 0;
  @*/
void f(int n, int* non_det_y) {
  int i=0, x=0, y=0;
  for(i=0; i<n; i++)
  {
    x = x-y;
    //@ assert(x==0);
    y = non_det_y[i];
    x = x+y;
    //@ assert(x!=0);
  }
  //@ assert(x==0);
}

