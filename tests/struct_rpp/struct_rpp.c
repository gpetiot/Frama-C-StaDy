
/* run.config
STDOPT: +"-main relational_wrapper_1 -stady -stady-msg-key generated-c,generated-pl -then -report"
*/

struct MyClass {
   int Name ;
};
/*@ ensures \old(x) < \old(y) ⇒ \result ≡ -1;
    ensures \old(x) > \old(y) ⇒ \result ≡ 1;
    ensures \old(x) ≡ \old(y) ⇒ \result ≡ 0;
    assigns \result;
    assigns \result \from x, y;
 */
int IntCompare(int x, int y)
{
  int __retres;
  if (x < y) {
    __retres = -1;
    goto return_label;
  }
  if (x > y) {
    __retres = 1;
    goto return_label;
  }
  __retres = 0;
  return_label: return __retres;
}

/*@ requires \valid(t + (0 .. 2));
    requires \valid(t + (0 .. 2)); */
void relational_wrapper_1(struct MyClass x1, struct MyClass x2, int *t)
{
  int return_variable_relational_2 = 0;
  int return_variable_relational_1 = 0;
  {
    int __retres_1;
    int tmp_1;
    /*@ assert Rpp: \valid(t + (0 .. 2)); */
    int x_1 = x1.Name;
    int y_1 = x2.Name;
    int i_1 = 0;
    /*@ loop invariant 0 ≤ i_1 ≤ 3;
        loop invariant
          ∀ ℤ k; 0 ≤ k < i_1 ⇒ *(t + k) ≢ x_1 ∧ *(t + k) ≢ y_1;
        loop assigns i_1;
    */
    while (i_1 < 3) {
      if (*(t + i_1) == x_1) {
        __retres_1 = 1;
        goto return_label_label_1;
      }
      if (*(t + i_1) == y_1) {
        __retres_1 = -1;
        goto return_label_label_1;
      }
      i_1 ++;
    }
    tmp_1 = IntCompare(x_1,y_1);
    __retres_1 = tmp_1;
    return_label_label_1: return_variable_relational_1 = __retres_1;
  }
  {
    int __retres_2;
    int tmp_2;
    /*@ assert Rpp: \valid(t + (0 .. 2)); */
    int x_2 = x2.Name;
    int y_2 = x1.Name;
    int i_2 = 0;
    /*@ loop invariant 0 ≤ i_2 ≤ 3;
        loop invariant
          ∀ ℤ k; 0 ≤ k < i_2 ⇒ *(t + k) ≢ x_2 ∧ *(t + k) ≢ y_2;
        loop assigns i_2;
    */
    while (i_2 < 3) {
      if (*(t + i_2) == x_2) {
        __retres_2 = 1;
        goto return_label_label_2;
      }
      if (*(t + i_2) == y_2) {
        __retres_2 = -1;
        goto return_label_label_2;
      }
      i_2 ++;
    }
    tmp_2 = IntCompare(x_2,y_2);
    __retres_2 = tmp_2;
    return_label_label_2: return_variable_relational_2 = __retres_2;
  }
  /*@ assert
      Rpp: return_variable_relational_1 ≡ -return_variable_relational_2;
  */
  return;
}

