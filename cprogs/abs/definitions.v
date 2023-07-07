Require Import utils.VSTALib.
Require Import cprogs.abs.program.
Local Open Scope logic.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Notation "'IntRepr'" := (Int.repr).
Notation "'Zabs'" := (Z.abs).
Notation "'INT_MAX'" := (Int.max_signed).
