
/* run.config
STDOPT: +"-main delete_substr -stady -stady-msg-key generated-c,generated-pl -then -report"
*/

/*@ requires 0 < sublen <= strlen;
  @ requires \valid(str + (0..strlen-1));
  @ requires \valid(substr + (0..sublen-1));
  @ assigns \nothing;
  @ behavior present:
  @   assumes \exists integer i; 0 <= i < strlen-sublen && 
  @     ( \forall integer j; 0 <= j < sublen ==> str[i+j] == substr[j] );
  @   ensures 0 <= \result < strlen-sublen;
  @   ensures \forall integer j; 0 <= j < sublen ==> str[\result+j] ==substr[j];
  @ behavior not_present:
  @   assumes \forall integer i; 0 <= i < strlen-sublen ==> 
  @     ( \exists integer j; 0 <= j < sublen && str[i+j] != substr[j] );
  @   ensures \result == -1;
  @*/
int find_substr(char *str, int strlen, char *substr, int sublen) {
  int i = 0;
  /*@ loop invariant 0 <= i <= strlen-sublen;
    @ loop invariant \forall integer k; 0 <= k < i ==>
    @          (\exists integer l; 0 <= l < sublen && str[k+l] != substr[l]);
    @ loop assigns i;
    @ loop variant strlen-sublen-i;
    @*/
  for(i = 0; i < strlen-sublen; i++) {
    int j = 0;
    /*@ loop invariant 0 <= j <= sublen;
      @ loop invariant \forall integer k; 0 <= k < j ==> str[i+k] == substr[k];
      @ loop assigns j;
      @ loop variant sublen-j;
      @*/
    for(j = 0; j < sublen; j++) {
      if(str[i+j] != substr[j]) {
	break;
      }
    }
    if (j == sublen)
      return i;
  }
  return -1;
}


/*@ requires 0 < sublen <= strlen;
  @ requires \valid(str + (0..strlen-1));
  @ requires \valid(dest + (0..strlen-1));
  @ requires \valid(substr + (0..sublen-1));
  @ requires \separated(dest+(0..strlen-1), substr+(0..sublen-1));
  @ requires \separated(dest+(0..strlen-1), str+(0..strlen-1));
  @ typically strlen <= 2;
  @ assigns dest[0..strlen-1];
  @ behavior not_present:
  @   assumes !(\exists integer i; 0 <= i < strlen-sublen && 
  @     ( \forall integer j; 0 <= j < sublen ==> str[i+j] == substr[j] ));
  @   ensures ( \forall integer k; 0 <= k < strlen ==> \old(str[k]) == dest[k] );
  @   ensures \result == 0;
  @ behavior present:
  @   assumes \exists integer i; 0 <= i < strlen-sublen && 
  @     ( \forall integer j; 0 <= j < sublen ==> str[i+j] == substr[j] );
  @   ensures \exists integer i; 0 <= i < strlen-sublen &&
  @     (( \forall integer j; 0 <= j < sublen ==> \old(str[i+j]) == \old(substr[j]) ) &&
  @     ( \forall integer k; 0 <= k < i ==> \old(str[k]) == dest[k] ) &&
  @     ( \forall integer l; i <= l < strlen-sublen ==> \old(str[l+sublen]) == dest[l] ) );
  @   ensures \result == 1; */
int delete_substr(char *str, int strlen, char *substr, int sublen, char *dest) {
  int start = find_substr(str, strlen, substr, sublen), j, k;
  if(start == -1) {
    /*@ loop invariant \forall integer m; 0 <= m < k ==> dest[m] == \at(str[m],Pre);
      @ loop invariant 0 <= k < strlen;
      @ loop assigns k, dest[0..strlen-1];
      @ loop variant strlen-k; */
    for( k = 0; k < strlen; k ++ ) dest[k] = str[k];
    return 0;
  }
  for( j = 0; j < start; j ++ ) dest[j] = str[j];
  for( j = start; j < strlen-sublen; j ++ ) dest[j] = str[j+sublen];
  return 1;
}
