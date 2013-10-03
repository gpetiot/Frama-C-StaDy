
/*@ requires \valid(in+(0..10));
  @*/
int f (char in[11])
{
  //char in[11]; // = "3277192070";
  char *s;
  unsigned char c;
  unsigned int i, j;
  int idx_in;
  in[10] = 0;
  idx_in = 0;
  s = in;
  i = 0;
  c = in[idx_in];
  /*@ loop invariant \forall int x; 0 <= x < idx_in ==> '0' <= in[x] && in[x] <= '9';
    @ loop invariant 0 <= i;
    @ loop variant 11-idx_in;
    @*/
  while (('0' <= c) && (c <= '9'))
  {
    j = c - '0';
    i = i * 10 + j;
    idx_in++;
    c = in[idx_in];
  }
  /* OK */
  //@ assert (i >= 0);
  return 0;
}

