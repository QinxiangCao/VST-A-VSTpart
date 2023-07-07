Require Import utils.VSTALib.
Require Import cprogs.swap.program.
Local Open Scope logic.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Notation "'IntRepr'" := (Int.repr).
Notation "'store_int' p x" :=
  (@data_at CompSpecs Tsh tint (Vint(IntRepr(x))) p)
  (x at level 0, p at level 0, at level 0).
Notation "'store_int_pair' p x y" :=
  (@data_at CompSpecs Tsh (Tstruct _int_pair noattr) (Vint(IntRepr(x)), Vint(IntRepr(y))) p)
  (x at level 0, y at level 0, p at level 0, at level 0).

