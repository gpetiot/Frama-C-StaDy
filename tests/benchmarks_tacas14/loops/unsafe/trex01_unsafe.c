
_Bool T[1000];
int G = 0;

void f(int d, int x, int y, int k) {
  int z = 1;
  L1:
  while (z < k) { z = 2 * z; }
  //@ assert(z>=2);
  L2:
  while (x > 0 && y > 0) {
    _Bool c = T[G++];
    if (c) {
      P1:
      x = x - d;
      y = T[G++];
      z = z - 1;
    } else {
      y = y - d;
    }
  }
}

/*@ requires k < 20;
  @ requires x < 20;
  @ requires y < 20;
  @*/
void m(_Bool c, int x, int y, int k) {
  if (c) {
    f(1, x, y, k);
  } else {
    f(2, x, y, k);
  }
}


