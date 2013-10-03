
typedef int Char;

Char *tmp;

int glob2 (Char *pathbuf, Char *pathlim)
{
  Char *p;

  for (p = pathbuf; p <= pathlim; p++) {
    //@ assert(p<=tmp);
    *p = 1;
  }

  return 0;
}

/*@ requires MAXPATHLEN == 1;
  @ requires \valid(pathbuf+(0..MAXPATHLEN));
  @*/
int f (unsigned MAXPATHLEN, Char* pathbuf)
{
  Char *bound = pathbuf + sizeof(pathbuf)/sizeof(*pathbuf) - 1;

  tmp = pathbuf + sizeof(pathbuf)/sizeof(*pathbuf) - 1;

  glob2 (pathbuf, bound);

  return 0;
}
