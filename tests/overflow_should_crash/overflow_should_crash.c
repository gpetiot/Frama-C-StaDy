
/* run.config
OPT: -main f -pp-annot -stady -stady-msg-key generated-c,generated-pl -then -report
*/

#include <limits.h>

void f(int x) {
  //@ assert x+1 <= INT_MAX; // error when x = INT_MAX
}
