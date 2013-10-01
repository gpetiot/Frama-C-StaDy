

/*@ requires 0 <= SIZE;
  @ requires \valid(non_det_A+(0..SIZE-1));
  @*/
void f(int SIZE, int non_det_v, int* non_det_A)
{
  unsigned int SIZE=1;
  unsigned int j,k;
  int array[SIZE], menor;
  
  menor = non_det_v;

  for(j=0;j<SIZE;j++) {
       array[j] = non_det_A[j];
       
       if(array[j]<=menor)
          menor = array[j];                          
    }                       
    
  //@ assert array[0] > menor;
}

