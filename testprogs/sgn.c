//* demo for multi-cond

int sgn (int x) {
  //@ With x:Z,
  //@ Require PROP (Int.min_signed <= x <= Int.max_signed) LOCAL (temp _x  (Vint (Int.repr x))) SEP ()
  //@ Ensure PROP () LOCAL (temp ret_temp  (Vint (Int.repr (sgn x)))) SEP ()
  int ret;
  /*@ Assert
        (EX x',
   PROP (Int.min_signed <= x' <= Int.max_signed /\ x = x')
   LOCAL (temp _x  (Vint (Int.repr x'))) 
   SEP ()
   )%assert
  */
  if (x <= 0) {
    if(x == 0)
      ret = 0;
    else
      ret = -1;
  }
  else
    ret = 1;
  /*@ Assert
  ( EX r,
    PROP (r = sgn x') LOCAL (temp _x  (Vint (Int.repr x'))) SEP ())
  */
  return ret;
}
