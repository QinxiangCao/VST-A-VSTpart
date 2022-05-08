int is_leap_year(int year) {
    //@ With year : Z,
    /*@ Require
      PROP (Int.min_signed <= year <= Int.max_signed)
      LOCAL (temp _year (Vint (Int.repr year)))
      SEP ()
    */
    /*@ Ensure
      PROP ()
      LOCAL (temp ret_temp (Val.of_bool (is_leap_year year)))
      SEP ()
    */
    return year%4 == 0 && year%100 != 0 || year%400 == 0;
}
