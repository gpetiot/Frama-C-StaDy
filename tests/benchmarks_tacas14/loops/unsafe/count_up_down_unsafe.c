

void f(unsigned int nondet_uint)
{
  unsigned int n = nondet_uint;
  unsigned int x=n, y=0;
  while(x>0)
  {
    x--;
    y++;
  }
  //@ assert y!=n;
}
