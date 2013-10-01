

/*@ requires 0 < MAX <= 10;
  @ requires \valid(str1+(0..MAX-1));
  @ requires \valid(str2+(0..MAX-1));
  @*/
void f(unsigned int MAX, char* str1, char* str2) {
    int cont, i, j;
    cont = 0;
    
    str1[MAX-1]= '\0';

    j = 0;
    
    for (i = MAX - 1; i >= 0; i--) {
        str2[j] = str1[0];
        j++;
    }

    j = MAX-1;
    for (i=0; i<MAX; i++) {
      //@assert(str1[i] == str2[j]);
      j--;
    }
}
