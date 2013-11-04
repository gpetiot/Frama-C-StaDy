
#define DEBUG

#ifdef DEBUG
extern void printf(const char*, ...);
#endif


typedef int addr;


void* my_malloc(char* mem, int* dec, int* inc, int max_len, unsigned n) {
  int i, k, j, can_store, ret = 0;
  for(i = 1; i < max_len; i++) {
    /* pas assez de place dans le tableau */
    if(i+n > max_len)
      break;
    can_store = 1;
    /* on cherche n cases libres consécutives */
    for(k = 0; k < n && can_store; k++) {
      if(dec[i+k] != 0)
	can_store = 0;
    }
    /* si on a trouvé n cases libres consécutives */
    if(can_store) {
      /* on les occupe */
      for(j = 0; j < n; j++) {
	dec[i+j] = n-j;
	inc[i+j] = j;
      }
      /* on retourne l'adresse de la première case */
      ret = mem+i;
      break;
    }
  }
#ifdef DEBUG
  printf("my_malloc(%i) = %p\n", n, ret);
#endif
  return ret;
}




void my_free(char* mem, int* dec, int* inc, int max_len, void *ptr) {
  int ind = (char*)ptr - mem, n, i;
  n = dec[ind];
  for(i = 0; i < n; i++)
    dec[ind+i] = inc[ind+i] = 0;
}



int my_valid(char* mem, int* dec, int* inc, int max_len, void *ptr) {
  int ind = (char*)ptr - mem, ret;
  ret = (dec[ind] > 0) ? 1 : 0;
#ifdef DEBUG
  printf("my_valid(%i) = %i\n", ind, ret);
#endif
  return ret;
}


int my_valid_interval(char* mem, int* dec, int* inc, int max_len,
		      void *ptr, unsigned beg, unsigned end) {
  int ind = (char*)ptr - mem, ret;
  ret = (dec[ind+beg] >= end) ? 1 : 0;
#ifdef DEBUG
  printf("my_valid_interval(%i) = %i\n", ind, ret);
#endif
  return ret;
}


char* my_base_addr(char* mem, int* dec, int* inc, int max_len, void* ptr) {
  int ind = (char*)ptr - mem;
  char* ret;
  ret = mem + ind - (inc[ind]-1);
#ifdef DEBUG
  printf("my_base_addr(%i) = %i\n", ind, ret-mem);
#endif
  return ret;
}


int my_block_length(char* mem, int* dec, int* inc, int max_len, void* ptr) {
  int ind = (char*)ptr - mem, ret;
  ret = (dec[ind] == 0) ? 0 : (dec[ind] + inc[ind] - 1);
#ifdef DEBUG
  printf("my_block_length(%i) = %i\n", ind, ret);
#endif
  return ret;
}



int my_offset(char* mem, int* dec, int* inc, int max_len, void* ptr) {
  int ind = (char*)ptr - mem, ret;
  ret = inc[ind] - 1;
#ifdef DEBUG
  printf("my_offset(%i) = %i\n", ind, ret);
#endif
  return ret;
}










/* for pre-condition */
int pvalid(int* dec, int* inc, int x) { return dec[x] > 0; }
int pvalid_interval(int* dec, int* inc, int x, int y) {
  return dec[x] > 0 && dec[y] > 0 && dec[x] == dec[y]+y-x; }
int pblock_length(int* dec, int* inc, int x) {
  if(dec[x] == 0) return 0; else return dec[x]+inc[x]-1; } 
int pbase_addr(int* dec, int* inc, int x) {
  if(inc[x] == 0) return -1; else return x-inc[x]+1; }
int poffset(int* dec, int* inc, int x) { return inc[x]-1; }




int f_precond(char *mem, int *dec, int *inc, int max_len, int n, int m) {
  int i;

  if(pathcrawler_dimension(inc) <= m) return 0;
  if(pathcrawler_dimension(inc) <= n) return 0;

  
  for(i = 1; i < max_len; i++) {
    if(i > 1)
      if(dec[i-1] > 1)
	if(dec[i] != dec[i-1]-1)
	  return 0;
  }
  
  for(i = 1; i < max_len; i++) {
    if(i == 1) {
      if(dec[i] == 0) {
	if(inc[i] != 0)
	  return 0;
      }
      else
	if(inc[i] != 1)
	  return 0;
    }
    else {
      if(dec[i] == 0)
	if(inc[i] != 0)
	  return 0;

      if(dec[i] == dec[i-1]-1) {
	if(inc[i] != inc[i-1]+1)
	  return 0;
      }
      else
	if(inc[i] != 1)
	  return 0;
    }
  }

#ifdef DEBUG
  printf("----------------------------\n");
  printf("n: %i\n", n);
  printf("m: %i\n", m);
  printf("dec: ");
  for(i = 1; i < max_len; i++)
    printf("|%2i",dec[i]);
  printf("\n");
  printf("inc: ");
  for(i = 1; i < max_len; i++)
    printf("|%2i",inc[i]);
  printf("\n");
#endif

  return 1;
}


/* fonction sous test */
int g(char* mem, int* dec, int* inc, int max_len, char* n, char* m) {
  int* t, i;

  //pathcrawler_assert(my_offset(mem, dec, inc, max_len, n) == 2);
  
  t = my_malloc(mem, dec, inc, max_len, 4);

  pathcrawler_assert(t-mem != 0);
  //my_free(mem, dec, inc, max_len, t);
  

  return 0;
}




/* driver perso */
int f(char *mem, int *dec, int *inc, int max_len, int n, int m) {
  return g(mem, dec, inc, max_len, mem+n, mem+m);
}

