Require Import ZArith.

Open Scope Z_scope.
Open Scope bool_scope.

Definition is_leap_year (year : Z) : bool :=
  (year mod 4 =? 0) && negb (year mod 100 =? 0) || (year mod 400 =? 0).
