struct int_pair {
  int a;
  int b;
};

void int_swap (int * px, int * py) {
  /*@ With x y px0 py0
      Require
        px == px0 && py == py0 &&
        store_int(px0, x) * store_int(py0, y)
      Ensure
        store_int(px0, y) * store_int(py0, x)
   */
  int t;
  t = * px;
  * px = * py;
  * py = t;
}

void int_pair_swap (struct int_pair * p) {
  /*@ With x y p0
      Require
        p == p0 &&
        store_int_pair(p0, x, y)
      Ensure
        store_int_pair(p0, y, x)
   */
  int t;
  t = p -> a;
  p -> a = p -> b;
  p -> b = t;
}

void int_pair_swap2 (struct int_pair * p) {
  /*@ With x y p0
      Require
        p == p0 &&
        store_int_pair(p0, x, y)
      Ensure
        store_int_pair(p0, y, x)
   */
  int_swap (& (p -> a), & (p -> b));
}

void int_swap_arith (int * px, int * py) {
  /*@ With x y px0 py0
      Require
        0 <= x && x <= 100 &&
        0 <= y && y <= 100 &&
        px == px0 && py == py0 &&
        store_int(px0, x) * store_int(py0, y)
      Ensure
        store_int(px0, y) * store_int(py0, x)
   */
  * px = * px + * py;
  * py = * px - * py;
  * px = * px - * py;
}

