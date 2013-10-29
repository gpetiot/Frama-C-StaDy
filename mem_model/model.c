
#define MAX_LEN 32
/*#define DEBUG*/

/*extern void printf(char*, ...);*/

/*char memory[MAX_LEN];
int len[MAX_LEN]; // nb de cases occupées à partir de cette case :
// 0: case libre
// 1: case occupée
// 2: cette case et la suivante occupées
// etc.
*/

void* my_malloc(char* memory, int* len, unsigned n) {
  int i, k, j, can_store;
#ifdef DEBUG
  printf("my_malloc(%i)\n", n);
#endif
  for(i = 0; i < MAX_LEN; i++) {
    /* pas assez de place dans le tableau */
    if(i+n > MAX_LEN)
      return 0;
    can_store = 1;
    /* on cherche n cases libres consécutives */
    for(k = 0; k < n && can_store; k++) {
      if(len[i+k] != 0)
	can_store = 0;
    }
    /* si on a trouvé n cases libres consécutives */
    if(can_store) {
      /* on les occupe */
      for(j = 0; j < n; j++)
	len[i+j] = n-j;
      /* on retourne l'adresse de la première case */
      return memory+i;
    }
    else
      ;
  }
  return 0;
}

/*@ predicate in_memory(char* memory, integer i, char* ptr) =
            \exists int k; 0 <= k < i && memory+k-ptr == 0;
*/


/*@ lemma not_valid_not_in_mem:
      \forall char* p, char* mem, integer i;
        !\valid(p) ==> !in_memory(mem, i, p);
*/


/*@ requires \valid_read(memory+(0..(MAX_LEN-1)));
  @ requires \valid_read(len+(0..(MAX_LEN-1)));
  @ ensures -1 <= \result < MAX_LEN;
  @ assigns \nothing;
  @ behavior found:
  @  assumes in_memory(memory, MAX_LEN, (char*)ptr);
  @  ensures memory+\result-ptr == 0;
  @ behavior not_found:
  @  assumes !in_memory(memory, MAX_LEN, (char*)ptr);
  @  ensures \result == -1;
  @ behavior invalid:
  @  assumes !\valid((char*)ptr);
  @  ensures \result == -1;
  @*/
int index_from_ptr(char* memory, int* len, void *ptr) {
  int i, ind = -1;
  /*@ loop invariant 0 <= i <= MAX_LEN;
    @ loop invariant -1 <= ind < MAX_LEN;
    @ loop invariant !in_memory(memory, i, (char*)ptr) ==> ind == -1;
    @ loop invariant \forall int k; 0 <= k < i ==> memory+k-ptr==0 ==> ind == k;
    @ loop invariant ind != -1 ==> memory+ind-ptr == 0;
    @ loop assigns i, ind;
    @ loop variant MAX_LEN-i;
    @*/
  for(i = 0; i < MAX_LEN && ind == -1; i++)
    /* pas sûr que PathCrawler apprécie cette instruction */
    if(memory+i-(char*)ptr == 0)
      ind = i;
#ifdef DEBUG
  printf("index_from_ptr(%p) = %i\n", ptr, ind);
#endif
  return ind;
}



void my_free(char* memory, int* len, void *ptr) {
  int ind = index_from_ptr(memory, len, ptr), n, i;
  /* pas dans la mémoire, on ne fait rien */
  if(ind == -1)
    return;
  /* on est au milieu d'un bloc */
  if(ind > 0 && len[ind-1] > 1)
    return;
  /* nombre de cases occupées */
  n = len[ind];
  for(i = 0; i < n; i++)
    len[ind+i] = 0;
}


/*@ requires \valid_read(memory+(0..(MAX_LEN-1)));
  @ requires \valid_read(len+(0..(MAX_LEN-1)));
  @ ensures \result == 1 <==> \valid((char*)ptr);
  @ behavior valid:
  @   assumes \valid((char*)ptr);
  @   ensures \result == 1;
  @ behavior not_valid:
  @   assumes !\valid((char*)ptr);
  @   ensures \result == 0;
  @*/
int my_valid(char* memory, int* len, void *ptr) {
  int ind = index_from_ptr(memory, len, ptr);
  /* pas dans la mémoire, pas valide */
  if(ind == -1)
    return 0;
  return len[ind] > 0;
}


int my_valid_interval(char* memory, int* len, void *ptr, unsigned beg,
		      unsigned end) {
  int ind = index_from_ptr(memory, len, ptr), i;
  /* pas dans la mémoire, pas valide */
  if(ind == -1)
    return 0;
  return len[ind+beg] >= end;
}


char* my_base_addr(char* memory, int* len, void* ptr) {
  int ind = index_from_ptr(memory, len, ptr), start, i;
  if(ind == -1)
    return 0;

  start = ind;
  for(i = start; i >= 0; i--)
    /* tant que l'élément à gauche dans len est strictement plus grand,
       on est dans le même bloc */
    if(len[i] > len[ind])
      ind = i;
  return memory+ind;
}


int my_block_length(char* memory, int* len, void* ptr) {
  int ind = index_from_ptr(memory, len, ptr);
  if(ind == -1)
    return 0;
  /* nombre de cases occupées à partir de la case courante */
  return len[ind];
}


int my_offset(char* memory, int* len, void* ptr) {
  int ind = index_from_ptr(memory, len, ptr), beg, start, i;
  if(ind == -1)
    return -1;
  
  beg = ind;
  start = ind;
  for(i = start; i >= 0; i--)
    /* tant que l'élément à gauche dans len est strictement plus grand,
       on est dans le même bloc */
    if(len[i] > len[beg])
      beg = i;

  /* beg est l'indice de l'adresse de base */
  return len[ind] - len[beg];
}



void debug(char* memory, int* len) {
#ifdef DEBUG
  int i;
  for(i = 0; i < MAX_LEN; i++)
    printf("%i ",len[i]);
  printf("\n");
#endif
}




/* pré-condition de notre driver, pas de la fonction sous test */
/*@ assigns \nothing;
  @ ensures \forall int k; 0 <= k < MAX_LEN ==> len[k] >= 0;
  @ ensures \forall int k; 1<=k<MAX_LEN ==> (len[k-1]>1 ==> len[k]==len[k-1]-1);
  @*/
int f_precond(char memory[MAX_LEN], int len[MAX_LEN], int n) {
  int i;
  /* memory peut contenir n'importe quoi */
  /* len doit respecter un invariant */
  /*@ loop invariant 0 <= i <= MAX_LEN;
    @ loop invariant \forall int k; 0 <= k < i ==> len[k] >= 0;
    @ loop invariant \forall int k; 1<=k<i ==>(len[k-1]>1==>len[k]==len[k-1]-1);
    @ loop assigns i;
    @ loop variant MAX_LEN-i;
    @*/
  for(i = 0; i < MAX_LEN; i++)
    if(len[i] < 0)
      return 0;
    else
      if(len[i] > MAX_LEN-i)
	return 0;
      else
	if(i > 0)
	  if(len[i-1] > 1)
	    if(len[i] != len[i-1]-1)
	      return 0;


  /*if(!my_valid_interval(memory, len, memory+n, 0, 4))
    return 0;*/

  if(my_offset(memory, len, memory+n) != 3)
    return 0;
  
  return 1;
}


/* fonction sous test */
int g(char memory[MAX_LEN], int len[MAX_LEN], int* ptr) {
  return 0;
}


/* driver perso */
int f(char memory[MAX_LEN], int len[MAX_LEN], int n) {
  return g(memory, len, memory+n);
}

















/*
void main() {
  int* t;
  char memory[MAX_LEN];
  int len[MAX_LEN];
  init(memory, len);

  t = my_malloc(memory, len, 4*sizeof(int));
  debug(memory, len);

#ifdef DEBUG
  //@ assert \valid(t+3);
  printf("\\valid(t+3) = %i\n", my_valid(memory, len, t+3));

  //@ assert !\valid(t+4);
  printf("!\\valid(t+4) = %i\n", !my_valid(memory, len, t+4));
#endif

  my_free(memory, len, t);
  debug(memory, len);

  }*/

