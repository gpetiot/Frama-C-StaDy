
/* run.config
STDOPT: +"-main main -stady -stady-msg-key generated-c,generated-pl -stady-stop-when-assert-violated -then -report"
*/

struct s {
  int t[10];
};

/*@ ensures \result == a.t[0];*/
int f(struct s a){
  return  a.t[0];
}

void main(struct s a){
  int b;
  b = f(a);
 /*@ assert b == a.t[1];*/
}
