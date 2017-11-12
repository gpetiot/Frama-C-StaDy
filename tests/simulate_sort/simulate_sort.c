
/* run.config
STDOPT: +"-stady -stady-sim-fct sort -stady-msg-key generated-c,generated-pl -variadic-no-translation"
*/

extern int printf (const char *, ...);
#define N 4

/*@
    requires \valid(a+(0..n-1));

    assigns a[0..n-1];

    ensures \forall integer i; 0 <= i < n-1 ==> a[i] <= a[i+1];
    ensures \forall integer i; 0 <= i < n ==>
            \numof(0, n-1, \lambda integer k; a[k] == a[i])
               ==
	    \numof(0, n-1, \lambda integer k; \old(a[k]) == a[i]);
*/
void sort(int* a, int n);

void main() {
  int t[N], t_before[N];
  int i, n = N;

  for(i = 0; i < n; i++) {
    t[i] = (13-i)*(((i%2)*2)-1);
    t_before[i] = t[i];
  }

  sort(t, n);

  printf("before:\t after:\n");
  for(i = 0; i < n; i++) {
    printf("%i \t %i\n", t_before[i], t[i]);
  }
  printf("\n");
}
