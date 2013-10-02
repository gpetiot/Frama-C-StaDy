
_Bool __VERIFIER_nondet_bool();

void f(int x, int y, int z)
{

  while(x<100 && 100<z) 
  {
    _Bool tmp=__VERIFIER_nondet_bool();
    if (tmp)
   {
     x++;
   }
   else
   {
     x--;
     z--;
   }
  }                       
    
  //@ assert(0);    
}


