/* run.config
OPT: -main f -stady -stady-msg-key generated-c -then -report
*/

/*@ requires -100 <= x <= 100;
  @ behavior pos:
  @   assumes 0 <= x <= 100;
  @ behavior neg:
  @   assumes -100 <= x < 0;
  @*/
void f(int x) {
  int y;
  
  /*@ behavior b1:
    @   assumes 5 <= x <= 10;
    @   ensures 10 <= y <= 20;
    @ behavior b2:
    @   assumes x != 0;
    @   ensures y != 0;
    @*/
  /*@ for pos:
    @   behavior b3:
    @     ensures 0 <= x <= 200;
    @*/
  /*@ for neg:
    @   behavior b4:
    @     ensures -200 <= x < 0;
    @*/
  /*@ for pos:
    @   behavior b5:
    @     assumes 0 <= x <= 50;
    @     ensures y <= 100;
    @*/
  y = x * 2;
}
