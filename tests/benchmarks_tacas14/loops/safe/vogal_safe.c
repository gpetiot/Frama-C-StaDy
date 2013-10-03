

/*@ requires \valid(input_string+(0..(MAX-1)));
  @ requires 0 <= MAX <= 3;
  @*/
void f(int MAX, char *input_string)
{
  char vogal_array[]={'a','A','e','E','i','I','o','O','u','U','\0'}; 
  unsigned int  i,j,cont, tam_string, n_caracter;

  input_string[MAX-1]='\0';
  
  n_caracter = 0;
  /*@ loop invariant 0 <= n_caracter < MAX;
    @ loop variant MAX-n_caracter;
    @*/
  while(input_string[n_caracter]!='\0')
    n_caracter++;

  cont = 0;
  /*@ loop invariant 0 <= i <= n_caracter;
    @ loop invariant 0 <= cont <= n_caracter*MAX/2;
    @ loop variant n_caracter-i;
    @*/
  for(i=0;i<n_caracter;i++)
    /*@ loop invariant 0 <= j <= MAX/2;
      @ loop invariant 0 <= cont <= i*MAX/2 + j;
      @ loop variant MAX/2 - j;
      @*/
    for(j=0;j<MAX/2;j++)
      if(input_string[i] == vogal_array[j])
	cont++;
           
  i=0;
  int cont_aux = 0;
  /*@ loop invariant 0 <= i <= MAX;
    @ loop invariant 0 <= cont_aux <= n_caracter*MAX/2;
    @ loop variant MAX-i;
    @*/
  while(input_string[i]!='\0')
    {
      /*@ loop invariant 0 <= j <= MAX/2;
	@ loop invariant 0 <= cont_aux <= i*MAX/2 + j;
	@ loop variant MAX/2 - j;
	@*/
      for(j=0;j<MAX/2;j++)
	{
	  if(input_string[i] == vogal_array[j])
	    cont_aux++;
	}       
      i++;       
    }    
  //@ assert(cont_aux==cont);                          
}

