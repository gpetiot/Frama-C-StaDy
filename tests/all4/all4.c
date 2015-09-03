/* run.config
STDOPT: +"-main F7 /usr/local/share/frama-c/builtin.c -cpp-extra-args=\"-I /usr/local/share/frama-c/\" -stady -stady-sim-fct Frama_C_interval -stady-stop-when-assert-violated -stady-msg-key generated-c,generated-pl"
*/

typedef double T1;
typedef int T2;
typedef int T3;
typedef T1 T4[2];
typedef T1 T5[12];
/*@ ensures \old(f1) <= \result <= \old(f2);
    assigns \nothing; */
extern int Frama_C_interval(int f1, int f2);

T1 F2(T1 f3, T5 *f4, T5 *f5);

T1 F3(T1 f6, T1 f7, T1 f8, T1 f9, T1 f10);

T1 F3(T1 f6, T1 f7, T1 f8, T1 f9, T1 f10)
{
  T1 V1;
  T1 V2;
  V2 = ((f6 - f7) * (f8 - f9)) * (f8 - f9);
  V1 = V2 + f9;
  return V1;
}

T1 F4(T1 f11);

T2 F5(T1 f12, T5 *f13);

T1 F6(T1 f14, T5 *f15, T5 *f16);

void F7(T1 f17, T1 f18, T5 *f19, T5 *f20);

T2 F5(T1 f12, T5 *f13)
{
  T2 V3;
  V3 = 5;
  return V3;
}

T1 F2(T1 f3, T5 *f4, T5 *f5)
{
  T3 V4;
  T3 V5;
  T1 V6;
  V5 = f3 < (*f4)[0];
  if (V5) V6 = (*f5)[0];
  else {
    V4 = f3 > (*f4)[11];
    if (V4) V6 = (*f5)[11]; else V6 = F6(f3,f4,f5);
  }
  return V6;
}

T1 F4(T1 f11)
{
  T3 V7;
  T1 V8;
  V7 = f11 >= 0.;
  if (V7) V8 = f11; else V8 = - f11;
  return V8;
}

T1 F6(T1 f14, T5 *f15, T5 *f16)
{
  T1 V9;
  T1 V10;
  T1 V11;
  T1 V12;
  T2 V13;
  T2 V14;
  T1 V15;
  V13 = F5(f14,f15);
  if (V13 == 0) V14 = 1; else V14 = V13;
  if (V14 == 12) V13 = 11; else V13 = V14;
  V14 = V13 - 1;
  V9 = (*f15)[V13];
  V11 = (*f16)[V13];
  V10 = (*f15)[V14];
  V12 = (*f16)[V14];
  V15 = F3(f14,V9,V10,V11,V12);
  return V15;
}

/*@ requires \valid(f19);
  @ requires \valid(*f19+(0..11));
  @ requires \valid(f20);
  @ requires \valid(*f20+(0..11)); */
void F7(T1 f17, T1 f18, T5 *f19, T5 *f20)
{
  T3 V16;
  T4 V17;
  T3 V18;
  T1 V19;
  T1 V20;
  T1 V21;
  int V22;
  V21 = f17 * 0.1;
  V19 = V21 - 0.1;
  V20 = F2(V19,f19,f20);
  V18 = f18 < - V20;
  if (! V18) {
    V16 = f18 < V20;
    if (V16) {
      V17[0] = - V20;
      V17[1] = V20;
      V22 = V17[0] + 1. <= V17[1];
      /*@ assert V22 != 0; */ ;
    }
  }
  return;
}

T5 G1;
T5 G2;
void F8(void)
{
  T1 V23;
  T1 V24;
  int V25;
  int V26;
  V25 = Frama_C_interval(0,1);
  if (V25) V23 = 0.5; else V23 = 5.;
  V26 = Frama_C_interval(0,1);
  if (V26) V24 = - 100.0; else V24 = 100.0;
  G1[0] = 0.;  G1[1] = 1.;  G1[2] = 2.;  G1[3] = 3.;  G1[4] = 4.;  G1[5] = 5.;  G1[6] = 6.;  G1[7] = 7.;  G1[8] = 8.;  G1[9] = 9.;
  G1[10] = 10.;  G1[11] = 11.;  G2[0] = 0.;  G2[1] = 1.;  G2[2] = 2.;  G2[3] = 3.;  G2[4] = 4.;  G2[5] = 5.;  G2[6] = 6.;  G2[7] = 7.;
  G2[8] = 8.;  G2[9] = 9.;  G2[10] = 10.;  G2[11] = 11.;
  F7(V23,V24,& G1,& G2);
  return;
}
