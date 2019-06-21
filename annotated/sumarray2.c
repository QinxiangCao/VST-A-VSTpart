#include <stddef.h>

unsigned sumarray(unsigned a[], int n) {
  /* Given (a : val) (sh : share) (contents : list Z) (size: Z), */
  int i; unsigned s;
  s=0;
  /* Inv (EX i,
    PROP  (0 <= i <= size)
    LOCAL (temp _a a;
          temp _i (Vint (Int.repr i));
          temp _n (Vint (Int.repr size));
          temp _s (Vint (Int.repr (sum_Z (sublist 0 i contents)))))
    SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a))
  */
  for (i=0; i<n; i++) {
    s += a[i];
  }
  {
  /* * Assert (
    PROP  ()
    LOCAL (temp _s (Vint (Int.repr (sum_Z contents))))
    SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a))
  */
  }
  return s;
}

unsigned four[4] = {1,2,3,4};

int main(void) {
  // Given gv: globals,
  unsigned s;
  s = sumarray(four+2,2);
  return (int)s;
}
