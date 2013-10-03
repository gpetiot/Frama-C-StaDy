
/*@ requires \valid(nondet_bool+(0..(x1+x2+x3+1)*2));
  @ requires x1 < 3;
  @ requires x2 < 3;
  @ requires x3 < 3;
  @*/
int f(unsigned int x1, unsigned int x2, unsigned int x3, int* nondet_bool)
{
  unsigned int d1=1, d2=1, d3=1;
  int c1, c2, i = 0;
  
  c1 = nondet_bool[i++];
  c2 = nondet_bool[i++];
  
  /*@ loop invariant 0 <= x1;
    @ loop invariant 0 <= x2;
    @ loop invariant 0 <= x3;
    @ loop variant x1+x2+x3;
    @*/
  while(x1>0 && x2>0 && x3>0)
  {
    if (c1) x1=x1-d1;
    else if (c2) x2=x2-d2;
    else x3=x3-d3;
    c1 = nondet_bool[i++];
    c2 = nondet_bool[i++];
  }

  //@ assert(x1==0 || x2==0 || x3==0);
  return 0;
}

