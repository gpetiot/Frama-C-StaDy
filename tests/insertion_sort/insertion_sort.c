

/*@ requires 0 <= LEN <= 5;
    requires \valid(A+(0..LEN-1));
    ensures
      \forall integer i;
        0 <= i && i < \old(LEN)-1 ==> *(\old(A)+i) <= *(\old(A)+(i+1));
 */
void insertion_sort(int *A, int LEN)
{
  int i = 0;

  /*@ loop invariant 0 <= i && i <= LEN; */
  while (i < LEN) {

    int valueToInsert;
    int holePos;
    //@ assert \valid_read(A+i);
    valueToInsert = *(A + i);
    holePos = i;

    /*@ loop invariant 0 <= holePos && holePos <= i; */
    while (holePos > 0 && valueToInsert < *(A + (holePos - 1))) {

      //@ assert \valid_read(A+(holePos-1));
      //@ assert \valid(A+holePos);
      *(A + holePos) = *(A + (holePos - 1));
      holePos --;
    }

    //@ assert \valid(A+holePos);
    *(A + holePos) = valueToInsert;
    i ++;
  }
  return;
}


