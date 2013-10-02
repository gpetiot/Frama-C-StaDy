
/*@ requires 0 <= SIZE < 5;
  @ requires \valid(v+(0..SIZE-1));
  @ ensures \forall int x; 0 <= x < SIZE-1 ==> v[x] <= v[x+1];
  @*/
int f(unsigned int SIZE, int* v) {
  int i, j, k, key;

  /*@ loop invariant 1 <= j <= SIZE;
    @ loop invariant \forall int x; 0 <= x < j-1 ==> v[x] <= v[x+1];
    @ loop variant SIZE-j;
    @*/
  for (j=1;j<SIZE;j++) {	  
    key = v[j];
    i = j - 1;
    /*@ loop invariant -1 <= i <= j-1;
      @ loop variant i;
      @*/
    while((i>=0) && (v[i]>key)) {
      v[i+1] = v[i];
      i = i - 1;
    }
    v[i+1] = key;
  }

  return 0;
}

