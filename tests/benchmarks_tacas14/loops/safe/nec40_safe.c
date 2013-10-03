

  char x[100], y[100];

void f(int k) {
  int i,j;
  
  i = 0;
  /*@ loop invariant 0 <= i < 100;
    @ loop variant 100-i;
    @*/
  while(x[i] != 0){
    y[i] = x[i];
    i++;
  }
  y[i] = 0;
  
  if(k >= 0 && k < i)
    if(y[k] != 0)
      //@ assert \false;
      ;
}
