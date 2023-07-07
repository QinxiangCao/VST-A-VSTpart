int abs(int x) {
  /*@ With x0
      Require
        - INT_MAX <= x0 &&
        x0 <= INT_MAX &&
        x == Vint (IntRepr (x0)) && emp
      Ensure
        __return == Vint (IntRepr (Zabs (x0))) && emp
   */
  if (x < 0) {
    return -x;
  }
  else {
    return x;
  }
}
