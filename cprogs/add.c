int add(int x, int y) {
  /*@ With x0 y0
      Require
        0 <= x0 && x0 <= 100 && 
        0 <= y0 && y0 <= 100 && 
        x == Vint (IntRepr (x0)) && y == Vint (IntRepr (y0)) && emp
      Ensure
        __return == Vint (IntRepr (x0 + y0)) && emp
   */
  int z;
  z = x + y;
  return z;
}

int slow_add(int x, int y) {
  /*@ With x0 y0
      Require
        0 <= x0 && x0 <= 100 && 
        0 <= y0 && y0 <= 100 && 
        x == Vint (IntRepr (x0)) && y == Vint (IntRepr (y0)) && emp
      Ensure
        __return == Vint (IntRepr (x0 + y0)) && emp
   */
  /*@ Inv
        exists x1 y1,
          0 <= x1 && x1 <= 100 &&
          0 <= x1 + y1 && x1 + y1 <= 200 &&
          x1 + y1 == x0 + y0 &&
          x == Vint (IntRepr (x1)) && y == Vint (IntRepr (y1)) && emp
   */
  while (x > 0) {
    x = x - 1;
    y = y + 1;
  }
  return y;
}

