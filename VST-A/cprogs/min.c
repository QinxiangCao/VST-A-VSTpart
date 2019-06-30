int minimum(int a[ ], int n) {
  // With (a: val) (n: Z) (al: list Z),
  /* Require
    PROP  (1 <= n <= Int.max_signed; Forall repable_signed al)
    LOCAL (temp _a a; temp _n (Vint (Int.repr n)))
    SEP   (data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a)
  */
  /* Ensure
    PROP ()
    LOCAL(temp ret_temp  (Vint (Int.repr (fold_right Z.min (hd 0 al) al))))
    SEP   (data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a)
  */
  int i, min;
  min=a[0];
  /* Inv EX i:Z,
    PROP(0 <= i <= n)
    LOCAL(temp _i (Vint (Int.repr i));
          temp _min (Vint (Int.repr (fold_right Z.min (Znth 0 al) (sublist 0 i al))));
          temp _a a;
          temp _n (Vint (Int.repr n)))
    SEP(data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a)
  */
  for (i=0; i<n; i++) {
    int j = a[i];
    int temp;
    if (j<min)
      temp = j;
    else
      temp = min;
    /* Assert
      PROP(0 <= i <= n)
      LOCAL(temp _i (Vint (Int.repr i));
            temp _temp (Vint (Int.repr (fold_right Z.min (Znth 0 al) (sublist 0 (i+1) al))));
            temp _a a;
            temp _n (Vint (Int.repr n)))
      SEP(data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a)
    */
    min = temp;
  }
  return min;
}
