

/*@ requires 1 <= n <= 7;
  @ requires \valid(a+(0..n-1));
  @ ensures (\forall int i; 0 <= i < n ==> a[i] != q) <==> \result == 0;
  @ ensures (\exists int i; 0 <= i < n && a[i] == q) <==> \result == 1;
  @*/
int linear_search(int *a, int n, int q) {
  unsigned int j=0;
  /*@ loop invariant 0 <= j <= n;
    @ loop invariant \forall int i; 0 <= i < j ==> a[i] != q;
    @ loop variant n-j;
    @*/
  while (j<n && a[j]!=q) {
    j++;
  }
  if (j<n) return 1;
  else return 0;
}

