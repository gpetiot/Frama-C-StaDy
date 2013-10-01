
unsigned int  SIZE;
int linear_search(int *a, int n, int q) {
  unsigned int j=0;
  while (j<n && a[j]!=q) {
    j++;
    if (j==20) j=-1;
  }
  if (j<SIZE) return 1;
  else return 0;
}

/*@ requires nondet_uint <= 500;
  @ requires \valid(a+(0..nondet_uint/2));
  @*/
void f(unsigned int nondet_uint, int* a) {
  int ret;
  SIZE=(nondet_uint/2)+1;
  a[SIZE/2]=3;
  ret =linear_search(a,SIZE,3);
  //@ assert ret == 1;
}
