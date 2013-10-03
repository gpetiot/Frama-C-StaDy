
/*@ requires M <= 7;
  @ requires \valid(A+(0..M-1));
  @ requires \valid(B+(0..M-1));
  @ requires \valid(C+(0..M-1));
  @*/
void f(unsigned int M, int* A, int* B, int* C)
{
  unsigned int  i;
  
  /*@ loop invariant 0 <= i <= M;
    @ loop invariant \forall int x; 0 <= x < i ==> C[x]==A[x]+B[x];
    @ loop variant M-i;
    @*/
  for(i=0;i<M;i++)
     C[i]=A[i] + B[i];
  
  //@ assert \forall int x; 0 <= x < M ==> (C[x]==A[x]+B[x]);
}

