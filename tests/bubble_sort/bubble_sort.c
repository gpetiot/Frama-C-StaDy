/*@ requires 0 <= l <= 3;
    requires \block_length(table) == l*sizeof(int);
    ensures
      \forall integer i;
        0 <= i < \old(l)-1 ==>
        *(\old(table)+i) >= *(\old(table)+(i+1));
 */
void bubblesort(int *table, int l)
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
    //@ assert 0 <= i <= l-1;
    //@ assert l-1-i >= 0;
    //@ ghost int old_variant;
    /*@ loop invariant 0 <= i <= l-1;
      @ loop variant l-1-i;
      @*/
    while (i < l - 1) {
      //@ ghost old_variant = l-1-i;
      if (*(table + i) < *(table + (i + 1))) {
        fini = (char)0;
        temp = *(table + i);
        *(table + i) = *(table + (i + 1));
        *(table + (i + 1)) = temp;
      }
      i ++;
      //@ assert 0 <= i <= l-1;
      //@ assert l-1-i < old_variant;
    }
    nb ++;
  }
  return;
}


