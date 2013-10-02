
/*@ requires N_LIN < 3;
  @ requires N_COL < 3;
  @ requires \valid(matriz+(0..N_COL-1));
  @ requires \forall int x; 0 <= x < N_COL ==> \valid(matriz[x]+(0..N_LIN-1));
  @*/
void f(unsigned int N_LIN, unsigned int N_COL, int maior, int** matriz)
{   
  unsigned int j,k;
  
  /*@ loop invariant 0 <= j <= N_COL;
    @ loop variant N_COL-j;
    @*/
  for(j=0;j<N_COL;j++) {
    /*@ loop invariant 0 <= k <= N_LIN;
      @ loop invariant \forall int x; 0 <= x < k ==> maior >= matriz[j][x];
      @ loop variant N_LIN-k;
      @*/
    for(k=0;k<N_LIN;k++)
    {       
       
       if(matriz[j][k]>=maior)
          maior = matriz[j][k];                          
    }
  }                    
    
  //@ assert(matriz[0][0]<=maior);    
}

