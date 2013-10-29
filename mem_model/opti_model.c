
#define PVALID(L,x) (L[x] > 0)
#define PVALID_INTERVAL(L,x,y) ((L[x] > 0 && L[y] > 0 && L[y] == L[x]+y-x))
  /* -1 pour rendre les contraintes unsat car \block_length doit etre appelé
     sur une adresse de base */
#define PBLOCK_LENGTH(L,x) ((x==0) ? L[x] : ((L[x-1] > L[x]) ? -1 : L[x]))
#define PBASE_ADDR(L,x) ((L[x]==0) ? 0 : (x+L[x]-1))
#define POFFSET(L,x) (L[x]-1)
#define PSEPARATED(x,y) (x != y)


int f_precond(char *mem, int *inc, int *dec, int max_len, int n, int m) {
  int i;

  //if(!PVALID(dec, n)) return 0;
  //if(!PVALID(dec, m)) return 0;
  //if(!PSEPARATED(n, m)) return 0;
  if(!PVALID_INTERVAL(dec, 2, 4)) return 0;
  //if(PBLOCK_LENGTH(dec, n) != 4) return 0;
  //if(PBASE_ADDR(inc, m) != n) return 0;
  //if(POFFSET(inc, m) != 7) return 0;

  for(i = 0; i < max_len; i++) {
    if(dec[i] > max_len-i)
      return 0;
    if(i > 0) {
      if(dec[i-1] > 1) {
	/* on doit décrémenter dec */
	if(dec[i] != dec[i-1]-1)
	  return 0;
	/* si on décrémente dec, on doit incrémenter inc */
	if(inc[i] != inc[i-1]+1)
	  return 0;
      }
    }
    if(dec[i] == 0)
      if(inc[i] != 0)
	return 0;
      else;
    else
      if(inc[i] != 1)
	return 0;
  }

  return 1;
}


/* driver perso */
int f(char *mem, int *inc, int *dec, int max_len, int n, int m) {
  return 0;
}

