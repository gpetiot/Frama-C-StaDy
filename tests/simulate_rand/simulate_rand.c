
/* run.config
STDOPT: +"-stady -stady-sim-fct rand -stady-msg-key generated-c,generated-pl -then -report"
*/

int rand();

void main() {
  int x = rand();
  int y = rand();
  int z = rand();

  //@ assert x == y;

  //@ assert x != z;
}
