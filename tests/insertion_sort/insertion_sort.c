
extern void printf(char * , ...);

/*@ requires 0 <= LEN && LEN <= 5;
    requires \block_length(A) == LEN*sizeof(int);
    ensures
      \forall integer i;
        0 <= i && i < \old(LEN)-1 ==> *(\old(A)+i) <= *(\old(A)+(i+1));
 */
void insertionsort(int *A, int LEN)
{
  int i = 0;

  /*@ loop invariant 0 <= i && i <= LEN; */
  while (i < LEN) {

    int valueToInsert;
    int holePos;
    valueToInsert = *(A + i);
    holePos = i;
    printf((char*)"boucle 1 (i = %i) (holePos = %i)\n", i, holePos);

    /*@ loop invariant 0 <= holePos && holePos <= i; */
    while (holePos > 0 && valueToInsert < *(A + (holePos - 1))) {

      printf((char*)"boucle 2 (i = %i) (holePos = %i)\n", i, holePos);
      *(A + holePos) = *(A + (holePos - 1));
      holePos --;

      printf((char*)"boucle 2 (i = %i) (holePos = %i)\n", i, holePos);

    }
    *(A + holePos) = valueToInsert;
    i ++;

    printf((char*)"boucle 1 (i = %i) (holePos = %i)\n", i, holePos);
  }
  return;
}


