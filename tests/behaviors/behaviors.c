
/* run.config
STDOPT: +"-main f -stady -stady-msg-key generated-c,generated-pl -then -report"
*/

/*@ behavior X:
  @   assumes x >= y;
  @   assumes x >= z;
  @   requires x >= 0;
  @   requires y >= 0;
  @   requires z >= 0;
  @   ensures y <= x && z <= x;
  @ behavior Y:
  @   assumes y >= x;
  @   assumes y >= z;
  @   requires x >= 0;
  @   requires y >= 0;
  @   requires z >= 0;
  @   ensures x <= y && z <= y;
  @ behavior Z:
  @   assumes z >= x;
  @   assumes z >= y;
  @   requires x >= 0;
  @   requires y >= 0;
  @   requires z >= 0;
  @   ensures x <= z && y <= z;
  @*/
void f(int x, int  y, int z) {
}
