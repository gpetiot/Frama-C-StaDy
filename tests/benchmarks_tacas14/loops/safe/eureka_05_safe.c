

/*@ requires n == 5;
  @ requires \valid(array+(0..n-1));
  @ ensures \forall int i; 0 <= i < n-1 ==> array[i] <= array[i+1];
  @*/
void SelectionSort(int n, int* array)
{
  int lh, rh, i, temp;

  /*@ loop invariant 0 <= lh <= n;
    @ loop variant n-lh;
    @*/
  for (lh = 0; lh < n; lh++) {
    rh = lh;
    /*@ loop invariant lh+1 <= i <= n;
      @ loop invariant \forall int x; lh <= x < i ==> array[rh] <= array[x];
      @ loop variant n-i;
      @*/
    for (i = lh + 1; i < n; i++) 
      if (array[i] < array[rh])
	rh = i;
    temp = array[lh];
    array[lh] = array[rh];
    array[rh] = temp;
  }
}
