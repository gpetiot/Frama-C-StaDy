
/*@ requires N_LIN < 3;
  @ requires N_COL < 3;
  @ requires \valid(matriz+(0..N_COL-1));
  @ requires \forall int x; 0 <= x < N_COL ==> \valid(matriz[x]+(0..N_LIN-1));
  @*/
void f(unsigned int N_LIN, unsigned int N_COL, int maior, int** matriz)
{
  unsigned int j,k;
  
  for(j=0;j<N_COL;j++)
    for(k=0;k<N_LIN;k++)
    {
       
       if(matriz[j][k]>maior)
          maior = matriz[j][k];                          
    }                       
    
  for(j=0;j<N_COL;j++)
    for(k=0;k<N_LIN;k++)
      //@ assert(matriz[j][k]<maior);
      ;
}

