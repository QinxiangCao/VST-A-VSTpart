int max3(int x, int y, int z) {
  /*@ With x0 y0 z0
      Require
        INT_MIN <= x0 && x0 <= INT_MAX &&
        INT_MIN <= y0 && y0 <= INT_MAX &&
        INT_MIN <= z0 && z0 <= INT_MAX &&
        x == Vint (IntRepr (x0)) &&
        y == Vint (IntRepr (y0)) &&
        z == Vint (IntRepr (z0)) &&
        emp
      Ensure
        exists r,
          r >= x0 &&
          r >= y0 &&
          r >= y0 &&
          __return == Vint (IntRepr (r)) &&
          emp
   */
  if (x < y)
    if (y < z)
      return z;
    else
      return y;
  else
    if (x < z)
      return z;
    else
      return x;
}
