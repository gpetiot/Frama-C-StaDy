
/*@ requires 1 <= n <= 5;
  @ requires \valid(t+(0..n-1));
  @ assigns t[0..n-1];
  @ ensures \forall int x; 0 <= x < n-1 ==> t[x] <= t[x+1];
  @*/
void insertion_sort(int t[], int n) {
  int i = 1,j;
  int mv;

  /*@ loop invariant 1 <= i <= n;
    @ loop invariant \forall int x; 0 <= x < i-1 ==> t[x] <= t[x+1];
    @ loop assigns i, j, mv, t[0..n-1];
    @ loop variant n-i;
    @*/
  for (; i<n; i++) {
    // assuming t[0..i-1] is sorted, insert t[i] at the right place
    mv = t[i]; 
    j = i;
    /*@ loop invariant 0 <= j <= i;
      @ loop invariant \forall integer k; j <= k < i ==> t[k] > mv;
      @ loop assigns j, t[0..n-1];
      @ loop variant j;
      @*/
    // look for the right index j to put t[i]
    for (; j > 0; j--) {
      if (t[j-1] <= mv) break;
      t[j] = t[j-1];
    }
    t[j] = mv;
  }
}
