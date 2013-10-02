
/*@ requires max == 5;
  @ requires \valid(str1+(0..max-1));
  @ requires \valid(str2+(0..max-1));
  @*/
void f(char* str1, char* str2, int max) {
  int i = max-1, j;

  str1[max-1]= '\0';

  j = 0;
   
  /*@ loop invariant -1 <= i;
    @ loop invariant i <= max-1;
    @ loop invariant i+j == max-1;
    @ loop variant i;
    @*/
  for (i = max - 1; i >= 0; i--) {
    str2[j] = str1[i];
    j++;
  }

  j = max-1;

  /*@ loop invariant 0 <= i <= max;
    @ loop invariant i+j == max-1;
    @ loop variant max-i;
    @*/
  for (i=0; i<max; i++) {
    //@ assert(str1[i] == str2[j]);
    j--;
  }   
}

