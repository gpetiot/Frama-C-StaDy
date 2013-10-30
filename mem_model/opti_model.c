
/*#define DEBUG*/

#ifdef DEBUG
extern void printf(const char*, ...);
#endif






void* my_malloc(char* mem, int* dec, int* inc, int max_len, unsigned n) {
  int i, k, j, can_store;
#ifdef DEBUG
  printf("my_malloc(%i)\n", n);
#endif
  for(i = 0; i < max_len; i++) {
    /* pas assez de place dans le tableau */
    if(i+n > max_len)
      return 0;
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
      return mem+i;
    }
  }
  return 0;
}

/*@ predicate in_mem(char* memory, integer i, char* ptr) =
      \exists int k; 0 <= k < i && memory+k-ptr == 0;
*/

/*@ predicate ind_in_mem(char* memory, integer i, char* ptr, integer k) =
      0 <= k < i && memory+k-ptr == 0;
*/


/*@ lemma not_valid_not_in_mem:
      \forall char* p, char* mem, integer i;
        !\valid(p) ==> !in_mem(mem, i, p);
*/

/*@ lemma not_valid_not_ind_in_mem:
      \forall char* p, char* mem, integer i, k;
        !\valid(p) ==> !ind_in_mem(mem, i, p, k);
*/


/*@ requires \valid_read(mem+(0..max_len-1));
  @ requires \valid_read(dec+(0..max_len-1));
  @ requires \valid_read(inc+(0..max_len-1));
  @ ensures -1 <= \result < max_len;
  @ assigns \nothing;
  @ behavior found:
  @  assumes in_mem(mem, max_len, (char*)ptr);
  @  ensures ind_in_mem(mem, max_len, (char*)ptr, \result);
  @ behavior not_found:
  @  assumes !in_mem(mem, max_len, (char*)ptr);
  @  ensures \result == -1;
  @ behavior invalid:
  @  assumes !\valid((char*)ptr);
  @  ensures \result == -1;
  @*/
int index_from_ptr(char* mem, int* dec, int* inc, int max_len, void *ptr) {
  int i, ind = -1;
  /*@ loop invariant 0 <= i <= max_len;
    @ loop invariant -1 <= ind < max_len;
    @ loop invariant !in_mem(mem, i, (char*)ptr) ==> ind == -1;
    @ loop invariant \forall int k;
                       ind_in_mem(mem, i, (char*)ptr, k) ==> ind == k;
    @ loop invariant ind != -1 ==> mem+ind-ptr == 0;
    @ loop assigns i, ind;
    @ loop variant max_len-i;
    @*/
  for(i = 0; i < max_len && ind == -1; i++)
    if(mem+i-(char*)ptr == 0)
      ind = i;
#ifdef DEBUG
  printf("index_from_ptr(%p) = %i\n", ptr, ind);
#endif
  return ind;
}



void my_free(char* mem, int* dec, int* inc, int max_len, void *ptr) {
  int ind = index_from_ptr(mem, dec, inc, max_len, ptr), n, i;
  /* pas dans la mémoire, on ne fait rien */
  if(ind == -1)
    return;
  /* on est au milieu d'un bloc */
  if(ind > 0 && dec[ind-1] > 1)
    return;
  /* nombre de cases occupées */
  n = dec[ind];
  for(i = 0; i < n; i++)
    dec[ind+i] = inc[ind+i] = 0;
}


/*@ requires \valid_read(mem+(0..max_len-1));
  @ requires \valid_read(dec+(0..max_len-1));
  @ requires \valid_read(inc+(0..max_len-1));
  @ ensures \result == 1 ==> \valid((char*)ptr);
  @ ensures !\valid((char*)ptr) ==> \result == 0;
  @ behavior invalid:
  @  assumes !in_mem(mem, max_len, (char*)ptr);
  @  ensures \result == 0;
  @ behavior valid:
  @  assumes in_mem(mem, max_len, (char*)ptr);
  @  ensures \exists int k; ind_in_mem(mem, max_len, (char*)ptr, k);
  @  ensures \exists int k;
       ind_in_mem(mem, max_len, (char*)ptr, k) && dec[k]>0 ==> \result == 1;
  @  ensures \exists int k;
       ind_in_mem(mem, max_len, (char*)ptr, k) && dec[k]==0 ==> \result == 0;
  @*/
int my_valid(char* mem, int* dec, int* inc, int max_len, void *ptr) {
  int ind = index_from_ptr(mem, dec, inc, max_len, ptr), ret;
  if(ind == -1)
    return 0;
  ret = (dec[ind] > 0)? 1: 0;
  return ret;
}


int my_valid_interval(char* mem, int* dec, int* inc, int max_len,
		      void *ptr, unsigned beg, unsigned end) {
  int ind = index_from_ptr(mem, dec, inc, max_len, ptr), i;
  if(ind == -1)
    return 0;
  return dec[ind+beg] >= end;
}


char* my_base_addr(char* mem, int* dec, int* inc, int max_len, void* ptr) {
  int ind = index_from_ptr(mem, dec, inc, max_len, ptr), ind_base_addr;
  if(ind == -1)
    return 0;
  ind_base_addr = ind - (inc[ind]-1);
  return mem + ind_base_addr;
}


int my_block_length(char* mem, int* dec, int* inc, int max_len, void* ptr) {
  int ind = index_from_ptr(mem, dec, inc, max_len, ptr), ind_base_addr;
  if(ind == -1)
    return 0;
  if(dec[ind] == 0)
    return 0;
  return dec[ind] + inc[ind] - 1;
}


/*@ requires \valid_read(mem+(0..max_len-1));
  @ requires \valid_read(dec+(0..max_len-1));
  @ requires \valid_read(inc+(0..max_len-1));
  @ assigns \nothing;
  @ behavior found:
  @  assumes in_mem(mem, max_len, (char*)ptr);
  @  ensures 0 <= \result < max_len;
  @ behavior not_found:
  @  assumes !in_mem(mem, max_len, (char*)ptr);
  @  ensures \result == -1;
  @*/
int my_offset(char* mem, int* dec, int* inc, int max_len, void* ptr) {
  int ind = index_from_ptr(mem, dec, inc, max_len, ptr), i;
  if(ind == -1)
    return -1;
  return inc[ind]-1;
}










/* for pre-condition */

int pvalid(int* dec, int* inc, int x) { return dec[x] > 0; }
int pvalid_interval(int* dec, int* inc, int x, int y) {
  return dec[x] > 0 && dec[y] > 0 && dec[x] == dec[y]+y-x;
}
int pblock_length(int* dec, int* inc, int x) {
  if(dec[x] == 0) return 0; else return dec[x]+inc[x]-1;
} 
int pbase_addr(int* dec, int* inc, int x) {
  if(inc[x] == 0) return -1; else return x-inc[x]+1;
}
int poffset(int* dec, int* inc, int x) { return inc[x]-1; }




int f_precond(char *mem, int *inc, int *dec, int max_len, int n, int m) {
  int i;

#ifdef DEBUG
  printf("dec: ");
  for(i = 0; i < max_len; i++)
    printf("|%2i",dec[i]);
  printf("\n");
  printf("inc: ");
  for(i = 0; i < max_len; i++)
    printf("|%2i",inc[i]);
  printf("\n");
  printf("----------------------------\n");
#endif

  
  if(pbase_addr(dec, inc, m) != m) return 0;
  if(pbase_addr(dec, inc, n) != n) return 0;
  //if(!pvalid_interval(dec, inc, m, m+4)) return 0;
  //if(!pvalid_interval(dec, inc, n, n+4)) return 0;
  if(n == m) return 0;
  
  
  for(i = 0; i < max_len; i++) {
    /*if(dec[i] > max_len-i)
      return 0;*/
    if(i == 0) {
      if(dec[0] == 0) {
	if(inc[0] != 0)
	  return 0;
      }
      else
	if(inc[0] != 1)
	  return 0;
    }
    else {
      if(dec[i-1] > 1)
	if(dec[i] != dec[i-1]-1)
	  return 0;
      if(dec[i] == dec[i-1]-1) {
	if(inc[i] != inc[i-1]+1)
	  return 0;
      }
      else
	if(dec[i] == 0) {
	  if(inc[i] != 0)
	    return 0;
	}
	else
	  if(inc[i] != 1)
	    return 0;
    }
  }

  /*
  for(i = 0; i < max_len; i++) {
    if(dec[i] > max_len-i)
      return 0;
    if(i > 0)
      if(dec[i-1] > 1)
	if(dec[i] != dec[i-1]-1)
	  return 0;
  }

  for(i = 0; i < max_len; i++) {
    if(i == 0) {
      if(dec[0] == 0) {
	if(inc[0] != 0)
	  return 0;
      }
      else
	if(inc[0] != 1)
	  return 0;
    }
    else {
      if(dec[i] == dec[i-1]-1) {
	if(inc[i] != inc[i-1]+1)
	  return 0;
      }
      else
	if(dec[i] == 0) {
	  if(inc[i] != 0)
	    return 0;
	}
	else
	  if(inc[i] != 1)
	    return 0;
    }
  }
  */

  return 1;
}


/* fonction sous test */
int g(char* mem, int* dec, int* inc, int max_len, char* n, char* m) {
  
}




/* driver perso */
int f(char *mem, int *inc, int *dec, int max_len, int n, int m) {
  return g(mem, inc, dec, max_len, mem+n, mem+m);
}

