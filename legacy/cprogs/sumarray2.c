#include <stddef.h>

unsigned sumarray(unsigned a[], int n) {
  /*@ With a sh contents size, */
  /*@ Require
      PROP  (readable_share sh; 0 <= size <= Int.max_signed)
      LOCAL (temp _a a; temp _n (Vint (Int.repr size)))
      SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)
  */
  /*@ Ensure
      PROP ()
      LOCAL(temp ret_temp  (Vint (Int.repr (sum_Z contents))))
      SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)
  */
  int i; unsigned s;
  s=0;
  /*@ Inv (EX i,
    PROP  (0 <= i <= size; Zlength contents = size)
    LOCAL (temp _a a;
          temp _i (Vint (Int.repr i));
          temp _n (Vint (Int.repr size));
          temp _s (Vint (Int.repr (sum_Z (sublist 0 i contents)))))
    SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a))
  */
  for (i=0; i<n; i++) {
    s += a[i];
  }
  return s;
}

unsigned four[4] = {1,2,3,4};

int main(void) {
  /*@ With gv, */
  /*@ Require
      main_pre prog tt nil gv
  */
  /*@ Ensure
      PROP()
      LOCAL (temp ret_temp (Vint (Int.repr (3+4))))
      SEP(TT)
  */
  unsigned s;
  s = sumarray(four+2,2);
  return (int)s;
}
