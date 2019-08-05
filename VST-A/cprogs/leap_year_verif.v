Require Import AClight.proofauto.
Require Import cprogs.leap_year_prog.
Require Import cprogs.leap_year_annot.
Require Import cprogs.leap_year_def.
Require Import AClight.advanced_forward.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Lemma mods_repr : forall i j,
  repable_signed i ->
  repable_signed j ->
  Int.mods (Int.repr i) (Int.repr j) = Int.repr (Z.rem i j).
Proof.
  intros.
  unfold Int.mods.
  autorewrite with norm.
  auto.
Qed.

Lemma rem_repable_signed_pos : forall i j,
  repable_signed j ->
  j > 0 ->
  repable_signed (Z.rem i j).
Proof.
  intros.
  destruct (Z_le_gt_dec i 0).
  - pose proof (Zquot.Zrem_lt_neg_pos i j ltac:(omega) ltac:(omega)).
    rep_omega.
  - pose proof (Zquot.Zrem_lt_pos_pos i j ltac:(omega) ltac:(omega)).
    rep_omega.
Qed.

Lemma rem_repable_signed_neg : forall i j,
  repable_signed j ->
  j < 0 ->
  repable_signed (Z.rem i j).
Proof.
  intros.
  destruct (Z_le_gt_dec i 0).
  - pose proof (Zquot.Zrem_lt_neg_neg i j ltac:(omega) ltac:(omega)).
    rep_omega.
  - pose proof (Zquot.Zrem_lt_pos_neg i j ltac:(omega) ltac:(omega)).
    rep_omega.
Qed.

Lemma rem_repable_signed : forall i j,
  repable_signed j ->
  j <> 0 ->
  repable_signed (Z.rem i j).
Proof.
  intros.
  destruct (Z_le_gt_dec j 0).
  - apply rem_repable_signed_neg; auto; omega.
  - apply rem_repable_signed_pos; auto; omega.
Qed.

Hint Rewrite mods_repr using rep_omega : norm.

Ltac assert_new_fact P :=
  first [
    assert P by assumption;
    fail 1
  | assert P
  ].

Ltac prove_new_fact P tac :=
  assert_new_fact P;
  only 1 : tac.

Ltac pose_new_fact H :=
  lazymatch type of H with
  | ?P =>
    assert_new_fact P;
    only 1 : exact H
  end.

Ltac pose_rem_repable_signeds :=
  repeat match goal with
  | |- context [Z.rem ?i ?j] =>
    pose_new_fact (rem_repable_signed i j ltac:(rep_omega) ltac:(rep_omega))
  | H : context [Z.rem ?i ?j] |- _ =>
    pose_new_fact (rem_repable_signed i j ltac:(rep_omega) ltac:(rep_omega))
  end.

Module Z.
Lemma eqb_true : forall n m,
  n = m ->
  (n =? m) = true.
Proof.
  intros.
  apply Z.eqb_eq.
  auto.
Qed.

Lemma eqb_false : forall n m,
  n <> m ->
  (n =? m) = false.
Proof.
  intros.
  apply Z.eqb_neq.
  auto.
Qed.

Lemma body_is_leap_year: semax_body Vprog Gprog f_is_leap_year is_leap_year_spec.
Proof.
  start_function f_is_leap_year_hint.
  forwardD.
  forwardD.
  { entailer!. inversion H0. inversion H2. }
  forwardD.
  forwardD.
  autorewrite with norm in H0.
  { entailer!. inversion H1. inversion H3. }
  forwardD.
  forwardD.
  
  intro d.
  remove_FF_precondition.
  revert  d.
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  intro d. forwardM_if. forwardM. forwardM.
  { entailer!. inversion H3. inversion H5. }
  { entailer!. inversion H1. inversion H3. }
  forwardD.
  - entailer!.
    unfold is_leap_year.
    autorewrite with norm in H0.
    pose_rem_repable_signeds.
    do_repr_inj H0.
    apply repr_inj_signed in H1. 2, 3 : rep_omega.
    rewrite Zquot.Zrem_Zmod_zero in * by rep_omega.
    rewrite eqb_true by auto.
    rewrite eqb_false by auto.
    simpl. auto.
  - entailer!.
    unfold is_leap_year.
    (* Mark *)
    (*
    unfold nullval, Archi.ptr64 in *.
    autorewrite with norm in H0.
    pose_rem_repable_signeds.
    do_repr_inj H0.
    *)
Abort.