
/*@ requires n < 20; */
void f(unsigned int n)
{
  unsigned int x=n, y=0;
  /*@ loop invariant 0 <= x <= n;
    @ loop invariant 0 <= y <= n;
    @ loop invariant x+y == n;
    @ loop variant x;
    @*/
  while(x>0)
  {
    x--;
    y++;
  }
  //@ assert(y==n);
}

