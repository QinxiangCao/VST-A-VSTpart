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
    int a = year + 1;
    int b = year % 4;
    int c = year % 100;
    int d = year % 400;
    return b == 0 && c != 0 || d == 0;
}
