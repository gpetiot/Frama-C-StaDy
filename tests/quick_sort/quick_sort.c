//  quickSort from http://alienryderflex.com/quicksort/
//
//  This public-domain C implementation by Darel Rex Finley.
//
//  * Returns YES if sort was successful, or NO if the nested
//    pivots went too deep, in which case your array will have
//    been re-ordered, but probably not sorted correctly.
//
//  * This function assumes it is called with valid parameters.
//
//  * Example calls:
//    quickSort(&myArray[0],5); // sorts elements 0, 1, 2, 3, and 4
//    quickSort(&myArray[3],5); // sorts elements 3, 4, 5, 6, and 7

#define MAX_LEVELS 100

/*@ requires 0 <= elements <= 3;
  @ requires \block_length(arr) == elements*sizeof(int);
  @ ensures \forall integer i; 0 <= i < elements-1 ==> arr[i] <= arr[i+1];
  //@ ensures \result == 0;
  @*/
int quicksort(int *arr, int elements) {
  int  piv, beg[MAX_LEVELS], end[MAX_LEVELS], i=0, L, R;

  beg[0]=0;
  end[0]=elements;

  while (i>=0) {
    L=beg[i];
    R=end[i]-1;
    if (L<R) {
      piv=arr[L];
      //if (i==MAX_LEVELS-1)
      //return -1;
      while (L<R) {
        while (arr[R]>=piv && L<R)
	  R--;
	if (L<R)
	  arr[L++]=arr[R];
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
#include <stdlib.h>
#include <stdio.h>

void main(int argc, char** argv) {
  int i;
  int * tab = malloc((argc-1)*sizeof(int));
  for(i = 1; i < argc; i++)
    tab[i-1] = atoi(argv[i]);
  quicksort(tab, argc-1);
  for(i = 0; i < argc-1; i++)
    printf("%i ", tab[i]);
  printf("\n");
  free(tab);
}
#endif
