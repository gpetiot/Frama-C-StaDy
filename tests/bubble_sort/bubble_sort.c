
/*@ requires 0 < n <= 5;
  @ requires \valid(A+(0..n-1));
  @ assigns A[0..n-1];
  @ ensures \forall integer i; 0 <= i < n-1 ==> A[i] <= A[i+1];
  @*/
void bubble_sort(int *A, int n) {
  int j , i ;
  j = i = 0;
  /*@ loop invariant 0 <= i <= n;
    @ loop assigns i, j, A[0..n-1];
    @ loop variant n-i;
    @*/
  for (i = 0; i < n ; i ++) {
    /*@ loop invariant 0 <= j <= n-i-1;
      @ loop invariant \forall integer a; 0 <= a <= j ==> A[a] <= A[j];
      @ loop assigns j, A[0..n-1];
      @ loop variant n-i-1-j;
      @*/
    for (j = 0; j < n-i-1; j ++) {
      if (A[j] > A[j+1]) {
	int x = A[j];
	A[j] = A[j+1];
	A[j+1] = x;
      }
    }
  }
}


