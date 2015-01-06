
/* run.config
STDOPT: +"-main f -stady -stady-msg-key generated-c,generated-pl -then -report"
*/

void f(int x) {
  if(x>0) {
    //@ assert x+1 > 0; // mathematically correct
  }
}
