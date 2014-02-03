
/* run.config
OPT: -main f -stady -stady-msg-key generated-c -then -report
*/

/*@ requires 0 <= n <= 6;
  @ requires \valid(t+(0..n-1));
  @ requires \forall integer i; 0 <= i < n ==> \valid(t[i]+(0..n-1));
  @ requires \forall integer i; 0 <= i < n ==>
  @               (\exists integer j; 0 <= j < n && (t[i][j] == 1 &&
  @               (\forall integer k; 0 <= k < n ==> k != j ==> t[i][k] == 0)));
  @*/
void f(int** t, int n) {
}
