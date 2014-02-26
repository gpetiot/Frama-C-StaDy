
/* run.config
OPT: -main merge_sort -stady -stady-msg-key generated-c,generated-pl -then -report
*/

/*@ requires \valid(A+(iLeft..iRight-1));
  @ requires \valid(B+(iLeft..iEnd-1));
  @*/
void BottomUpMerge(int* A, int iLeft, int iRight, int iEnd, int* B) {
  int i0 = iLeft, i1 = iRight, j;
 
  /* While there are elements in the left or right lists */
  /*@ loop invariant iLeft <= j <= iEnd;
    @ loop invariant iLeft <= i0 <= iRight;
    @ loop invariant iRight <= i1 <= iEnd;
    @ loop invariant i0-iLeft + i1-iRight == j-iLeft;
    @ loop assigns j, i0, i1, B[iLeft..iEnd-1];
    @ loop variant iEnd-j;
    @*/
  for (j = iLeft; j < iEnd; j++) {
    /* If left list head exists and is <= existing right list head */
    if (i0 < iRight && (i1 >= iEnd || A[i0] <= A[i1])) {
      B[j] = A[i0];
      i0 = i0 + 1;
    }
    else {
      B[j] = A[i1];
      i1 = i1 + 1;
    }
  }
}


/*@ requires \valid(A+(0..n-1));
  @ requires \valid(B+(0..n-1));
  @*/
void CopyArray(int* A, int* B, int n) {
  int i;
  /*@ loop invariant 0 <= i <= n;
    @ //loop invariant \forall integer k; 0 <= k < i ==> A[k] == B[k];
    @ loop assigns A[0..n-1], i;
    @ loop variant n-i;
    @*/
  for(i = 0; i < n; i++) {
    A[i] = B[i];
  }
}


int min(int x, int y) {
  return (x<=y) ? x : y;
}

/* array A[] has the items to sort; array B[] is a work array */
/*@ requires \valid(A+(0..n-1));
  @ requires \valid(B+(0..n-1));
  @*/
void BottomUpSort(int n, int* A, int* B) {
  int width;
 
  /* Each 1-element run in A is already "sorted". */
 
  /* Make successively longer sorted runs of length 2, 4, 8, 16...
     until whole array is sorted. */
  /*@ loop invariant 1 <= width <= 2*n - 1;
    @ loop variant n-width;
    @*/
  for (width = 1; width < n; width = 2 * width) {
    int i;
 
    /* Array A is full of runs of length width. */
    /*@ loop invariant 0 <= i <= n+2*width-1;
      @ loop variant n-i;
      @*/
    for (i = 0; i < n; i = i + 2 * width) {
      /* Merge two runs: A[i:i+width-1] and A[i+width:i+2*width-1] to B[] */
      /* or copy A[i:n-1] to B[] ( if(i+width >= n) ) */
      BottomUpMerge(A, i, min(i+width, n), min(i+2*width, n), B);
    }
 
    /* Now work array B is full of runs of length 2*width. */
    /* Copy array B to array A for next iteration. */
    /* A more efficient implementation would swap the roles of A and B */
    CopyArray(A, B, n);
    /* Now array A is full of runs of length 2*width. */
  }
}


/*@ requires 1 <= l <= 3;
  @ requires \separated(table,ret);
  @ requires \valid(table+(0..l-1));
  @ requires \valid(ret+(0..l-1));
  @ ensures \forall integer i; 0 <= i < l-1 ==> ret[i] <= ret[i+1];
  @*/
void merge_sort(int* table, int l, int* ret) {
  BottomUpSort(l, table, ret);
}





#ifdef _TEST
//#include <stdlib.h>
//#include <stdio.h>

extern void* malloc(unsigned int);
extern void free(void*);

void main(int argc, char** argv) {
  int i;
  int * tab = malloc((argc-1)*sizeof(int));
  int * ret = malloc((argc-1)*sizeof(int));
  //printf("argc-1 = %i\n", argc-1);
  for(i = 1; i < argc; i++)
    tab[i-1] = ret[i-1] = atoi(argv[i]);
  merge_sort(tab, argc-1, ret);
  //for(i = 0; i < argc-1; i++)
  //  printf("%i ", ret[i]);
  //printf("\n");
  free(tab);
  free(ret);
}
#endif
