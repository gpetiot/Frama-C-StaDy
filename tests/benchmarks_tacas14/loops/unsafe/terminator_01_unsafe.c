

void f(int x)
{
  int *p = &x;
 
  while(x<100) {
   (*p)++;
  }                       
  //@ assert(0);    
}

