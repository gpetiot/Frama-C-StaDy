
/* run.config
OPT: -main quick_sort -pp-annot -stady -stady-msg-key generated-c,generated-pl -then -report
*/

#define MAX_LEVELS 50

/*@ requires 0 <= elements;
  @ requires \valid(arr+(0..elements-1));
  @ requires \valid(beg+(0..99));
  @ requires \valid(end+(0..99));
  @ typically elements <= 3;
  @ ensures \forall integer i; 0 <= i < elements-1 ==> arr[i] <= arr[i+1];
  @ ensures \result == 0;
  @*/
int quick_sort(int *arr, int elements, int* beg, int* end) {
  int  piv, i=0, L, R;

  beg[0]=0;
  end[0]=elements;

  while (i>=0) {
    L=beg[i];
    R=end[i]-1;
    if (L<R) {
      piv=arr[L];
      if (i==MAX_LEVELS-1)
	return -1;

      /*@ loop invariant L <= R;
	@ loop variant R-L;
	@*/
      while (L<R) {
	/*@ loop invariant L <= R;
	  @ loop variant R-L;
	  @*/
        while (arr[R]>=piv && L<R)
	  R--;
	if (L<R)
	  arr[L++]=arr[R];
	/*@ loop invariant L <= R;
	  @ loop variant R-L;
	  @*/
        while (arr[L]<=piv && L<R)
	  L++;
	if (L<R)
	  arr[R--]=arr[L];
      }
      
      arr[L]=piv;
      beg[i+1]=L+1;
      end[i+1]=end[i];
      end[i++]=L;
    }
    else
      i--;
  }
  return 0;
}




#ifdef _TEST
void main(int argc, char** argv) {
  int i;
  int * tab = malloc((argc-1)*sizeof(int));
  for(i = 1; i < argc; i++)
    tab[i-1] = atoi(argv[i]);
  int beg[MAX_LEVELS], end[MAX_LEVELS];
  quick_sort(tab, argc-1, beg, end);
  for(i = 0; i < argc-1; i++)
    printf("%i ", tab[i]);
  printf("\n");
  free(tab);
}
#endif
