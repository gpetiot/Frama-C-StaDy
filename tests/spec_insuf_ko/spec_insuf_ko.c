
/* run.config
OPT: -main f -stady -stady-spec-insuf 28 -stady-msg-key generated-c,generated-pl -then -report
*/

/*@ requires n == 4;
  @ requires \valid(A+(0..n-1));
  @ assigns A[0..n-1];
  @// ensures \forall integer i; 0 <= i < n ==>
  @  //       \forall integer j; i <= j < n ==> A[i] <= A[j];
  @*/
void sort(int *A, int n)
{
  int c, position;
  for ( c = 0 ; c < ( n - 1 ) ; c++ ) {
    position = c;
    int d;
    for ( d = c + 1 ; d < n ; d++ ) {
      if ( A[position] > A[d] )
	position = d;
    }
    if ( position != c ) {
      int swap;
      swap = A[c];
      A[c] = A[position];
      A[position] = swap;
    }
  }
}

/*@ requires \valid(t+(0..k-1));
  @ requires k == 4;
  @ assigns t[0..k-1];
  @ ensures t[0] <= t[1];
  @*/
void f(int* t, int k) {
  sort(t, k);
}
