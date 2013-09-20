
/*@ requires 0 <= n <= 5;
  @ requires \valid(A+(0..n-1));
  @ requires \forall int i; 0 <= i < n-1 ==> A[i] <= A[i+1];
  @ ensures !(\forall integer i; 0 <= i < n ==> A[i] != elem) ==> \result == 1;
  @ ensures (\forall integer i; 0 <= i < n ==> A[i] != elem) ==> \result == 0;
  @*/
int binary_search( int* A, int n, int elem)
{ /* error undetected by path testing : low = 1 ; */
  int low, high, mid, ret ;
  low = 0 ;
  high = n-1 ;
  ret = 0 ;
  while( ( high > low ) )
    { mid = (low + high) / 2 ;
    
      /* error: should be: if( elem == A[mid] ) */
      /*if( elem != A[mid] ) */
      if( elem == A[mid] )
	ret = 1;
      if( elem > A[mid] )
        low = mid + 1 ;
      else
        high = mid - 1;
    }  
  mid = (low + high) / 2 ;
  /* error: should be: if( ( ret != 1)  && ( elem == A[mid]) ) */
  /*if( ( ret != 1)  && ( elem != A[mid]) )*/
  if( ( ret != 1)  && ( elem == A[mid]) )
    /* error: should be: ret =  1; */
    /*ret =  0; */
      ret = 1;
  
  return ret ;
}

