Require Import utils.VSTALib.
Require Import cprogs.add.program.
Local Open Scope logic.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Notation "'IntRepr'" := (Int.repr).
