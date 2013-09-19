

/*@ requires 0 <= LEN <= 5;
    requires \valid(A+(0..LEN-1));
    assigns A[0..LEN-1];
    ensures \forall integer i; 0 <= i < LEN-1 ==> A[i] <= A[i+1];
 */
void insertion_sort(int *A, int LEN)
{
  int i = 0;

  /*@ loop invariant 0 <= i <= LEN;
    @ loop invariant \forall integer a; 0 <= a < i ==> A[a] <= A[a+1];
    @ loop assigns i, A[0..LEN-1];
    @ loop variant LEN-i;
    @*/
  while (i < LEN) {

    int valueToInsert = A[i];
    int holePos = i;

    /*@ loop invariant 0 <= holePos <= i;
      @ loop assigns holePos, A[0..LEN-1];
      @*/
    while (holePos > 0 && valueToInsert < A[holePos - 1]) {
      A[holePos] = A[holePos - 1];
      holePos --;
    }

    A[holePos] = valueToInsert;
    i ++;
  }
  return;
}


