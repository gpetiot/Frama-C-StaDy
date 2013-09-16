/*@ requires 0 <= l <= 5;
    requires \valid(table+(0..l-1));
    ensures
      \forall integer i;
        0 <= i < \old(l)-1 ==>
        *(\old(table)+i) >= *(\old(table)+(i+1));
 */
void bubble_sort(int *table, int l)
{
  int i;
  int temp;
  int nb;
  char fini;
  fini = (char)0;
  nb = 0;
  while (! fini && (nb < l - 1)) {
    fini = (char)1;
    i = 0;
    /*@ loop invariant 0 <= i <= l-1;
      @ loop variant l-1-i;
      @*/
    while (i < l - 1) {
      if (*(table + i) < *(table + (i + 1))) {
        fini = (char)0;
        temp = *(table + i);
        *(table + i) = *(table + (i + 1));
        *(table + (i + 1)) = temp;
      }
      i ++;
    }
    nb ++;
  }
  return;
}


