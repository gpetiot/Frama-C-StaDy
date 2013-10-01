
/*@ requires 0 <= SIZE < 5;
  @ requires \valid(v+(0..SIZE-1));
  @*/
int f(unsigned int SIZE, int* v) {
  int i, j, k, key;
  for (j=1;j<SIZE;j++) {	  
    key = v[j];
    i = j - 1;
    while((i>=0) && (v[i]>key)) {
      if (i<2)
	v[i+1] = v[i];
      i = i - 1;
    }
    v[i+1] = key;	        
  }

  //@ assert \forall int k; 1 <= k < SIZE ==> (v[k-1]<=v[k]);

  return 0;
}
