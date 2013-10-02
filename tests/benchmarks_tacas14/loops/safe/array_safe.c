
/*@ requires \valid(array+(0..SIZE-1));
  @ requires 0 < SIZE <= 5;
  @*/
void f(int nondet_menor, int* array, unsigned int SIZE)
{
  unsigned int j,k;
  int menor = nondet_menor;
  
  /*@ loop invariant 0 <= j <= SIZE;
    @ loop invariant \forall int i; 0 <= i < j ==> menor <= array[i];
    @ loop variant SIZE-j;
    @*/
  for(j=0;j<SIZE;j++) {
       
       if(array[j]<=menor)
          menor = array[j];                          
    }                       
  //@ assert \forall int i; 0 <= i < SIZE ==> menor <= array[i];

  //@ assert(array[0]>=menor);    
}
