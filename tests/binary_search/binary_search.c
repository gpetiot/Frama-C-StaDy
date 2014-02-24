
/* run.config
OPT: -main binary_search -stady -stady-msg-key generated-c -then -report
*/

/* lemma div_by_2_def: \forall integer n; 0 <= n - 2 * (n / 2) <= 1; */

/*@ requires 0 < length <= 3;
    requires \valid(arr+(0..length-1));
    requires \forall integer j; 0 <= j < length-1 ==> arr[j] <= arr[j+1];
    assigns  \nothing;
    ensures -1 <= \result < length;
    ensures \result == -1 ==> \forall integer i; 0 <= i < length ==> arr[i] != query;
    ensures \result >= 0 ==> arr[\result] == query;
*/
int binary_search(int* arr, int length, int query) {
  int low = 0;
  int high = length - 1;
  /*@ loop invariant 0 <= low <= high+1;
    @ loop invariant low-1 <= high <= length-1;
    @ loop assigns high, low;
    @ loop variant high-low;
    @*/
  while (low <= high) {
    int mean = low + (high - low) / 2;
    //@ assert low <= mean <= high;
    //@ assert low < mean ==> \forall int x; 0 <= x < low ==> arr[x] != query;
    //@ assert mean+1 < high ==> \forall int x; high < x < length ==> arr[x] != query;
    if (arr[mean] == query) return mean;
    if (arr[mean] < query) low = mean + 1;
    else high = mean - 1;
  }
  return -1;
}

