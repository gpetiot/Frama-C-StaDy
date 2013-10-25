
#define MAX_LEN 64
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



int index_from_ptr(char* memory, int* len, void *ptr) {
  int i, ind = -1;
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
  for(i = beg; i < end; i++)
    if(ind+i >= MAX_LEN)
      return 0;
    else if(ind+i < 0)
      return 0;
    /* un des éléments de l'intervalle n'est pas valide */
    else if(len[ind+i] <= 0)
      return 0;
  /* tous les éléments sont valides */
  return 1;
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
int f_precond(char memory[MAX_LEN], int len[MAX_LEN], int n) {
  int i;
  /* memory peut contenir n'importe quoi */
  /* len doit respetcer un invariant */
  /*@ loop invariant \forall int k; 0 <= k < i ==> len[k] >= 0;
    @ loop invariant \forall int k; 1 <= k < i ==>
                                  (len[k] == 0 || len[k] == len[k-1]-1);
  */
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
  if(!my_valid_interval(memory, len, memory+n, 0, 4))
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

