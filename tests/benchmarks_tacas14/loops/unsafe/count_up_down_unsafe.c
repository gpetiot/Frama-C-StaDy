
/*@ requires n < 10; */
void f(unsigned int n)
{
  unsigned int x=n, y=0;
  while(x>0)
  {
    x--;
    y++;
  }
  //@ assert y!=n;
}
