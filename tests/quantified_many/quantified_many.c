/* run.config
STDOPT: +"-main f -stady -stady-msg-key generated-c,generated-pl -stady-prop A3,A4 -then -report"
*/

void f(int default_value) {
  int t[5][5];
  int min, i, j;

  for(i = 0; i < 5; i++)
    for(j = 0; j < 5; j++)
      t[i][j] = i+j;

  min = t[0][0];
  for(i = 0; i < 5; i++) {
    for(j = 0; j < 5; j++) {
      if(t[i][j] < min)
	min = t[i][j];
    }
  }

  /*@ assert A1: \forall integer a, integer b;
    @       0 <= a < 5 && 0 <= b < 5 ==> min <= t[a][b];
    @*/
  /*@ assert A2: \exists integer a, integer b;
    @       0 <= a < 5 && 0 <= b < 5 && min == t[a][b];
    @*/

  min = default_value;
  for(i = 0; i < 5; i++) {
    for(j = 0; j < 5; j++) {
      if(t[i][j] < min)
	min = t[i][j];
    }
  }

  /*@ assert A3: \forall integer a, integer b;
    @       0 <= a < 5 && 0 <= b < 5 ==> min <= t[a][b];
    @*/
  /*@ assert A4: \exists integer a, integer b;
    @       0 <= a < 5 && 0 <= b < 5 && min == t[a][b];
    @*/
}
