
/*@ requires M < 6;
  @ requires \valid(A+(0..M-1));
  @ requires \valid(B+(0..M-1));
  @ requires \valid(C+(0..M-1));
  @*/
void f(unsigned int M, int* A, int* B, int* C)
{
  unsigned int  i;
  

  for(i=0;i<M;i++)
     C[i]=A[i]+B[i];
  
  for(i=0;i<M;i++)
    //@ assert(C[i]==A[i]-B[i]);
    ;
}

