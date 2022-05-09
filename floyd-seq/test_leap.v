
Require Import VST.floyd.proofauto.
Require Import cprogs.mytest_prog.
Require Import cprogs.mytest_def.
Require Import FloydSeq.AClight.
Import AClightNotations.

Instance CompSpecs : compspecs. make_compspecs prog. Defined. 
Definition Vprog : varspecs. mk_varspecs prog. Defined.


Definition f_is_leap_year_spec_annotation :=
  ANNOTATION_WITH  year : Z, ((
      PROP (Int.min_signed <= year <= Int.max_signed)
      LOCAL (temp _year (Vint (Int.repr year)))
      SEP ()),
  (
      PROP ()
      LOCAL (temp ret_temp (Val.of_bool (is_leap_year year)))
      SEP ())).

Definition f_is_leap_year_spec_complex :=
  ltac:(uncurry_funcspec f_is_leap_year_spec_annotation).

Definition f_is_leap_year_funsig: funsig :=
  (((_year, tint) :: nil), tint).

Definition is_leap_year_spec :=
  ltac:(make_funcspec _is_leap_year f_is_leap_year_funsig f_is_leap_year_spec_complex).

Definition Gprog : funspecs :=
  ltac:(with_library prog [is_leap_year_spec]).


Lemma append_verif: 
  semax_body Vprog Gprog f_is_leap_year is_leap_year_spec.
Proof.
  leaf_function.
  floyd.forward.start_function.
  forward.
  admit.
  forward. admit.
  forward. admit.
  forward. admit.
  forward_if. admit.
  


