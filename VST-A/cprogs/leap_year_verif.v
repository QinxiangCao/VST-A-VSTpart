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
End Z.

(* override do_repr_inj to remove nullptr rules. *)
(*
Ltac do_repr_inj H ::=
   simpl typeof in H;
  try first [apply typed_true_of_bool in H
               |apply typed_false_of_bool in H
               | apply typed_true_negb_bool_val_p in H
               | apply typed_false_negb_bool_val_p in H; [| solve [auto]]
               | apply typed_false_negb_bool_val_p' in H
               | unfold nullval in H; (*simple*) apply typed_true_tint_Vint in H
               | unfold nullval in H; (*simple*) apply typed_false_tint_Vint in H
(*               | simple apply typed_true_tint in H *)
               ];
   rewrite ?ptrofs_to_int_repr in H;
   repeat (rewrite -> negb_true_iff in H || rewrite -> negb_false_iff in H);
   try apply int_eq_e in H;
   match type of H with
(*  don't do these, because they weaken the statement, unfortunately.
          | _ <> _ => apply repr_neq_e (*int_eq_false_e*) in H
          | _ <> _ => apply repr64_neq_e in H
*)
          | _ <> _ => let H' := fresh H "'" in assert (H' := repr_neq_e _ _ H)
          | _ <> _ => let H' := fresh H "'" in assert (H' := repr64_neq_e _ _ H)
          | Int.eq _ _ = false => apply int_eq_false_e in H
          | _ => idtac
  end;
  first [ simple apply repr_inj_signed in H; [ | rep_omega | rep_omega ]
         | simple apply repr_inj_unsigned in H; [ | rep_omega | rep_omega ]
         | simple apply repr_inj_signed' in H; [ | rep_omega | rep_omega ]
         | simple apply repr_inj_unsigned' in H; [ | rep_omega | rep_omega ]
         | simple apply ltu_repr in H; [ | rep_omega | rep_omega]
         | simple apply ltu_repr_false in H; [ | rep_omega | rep_omega]
         | simple apply ltu_inv in H; cleanup_repr H
         | simple apply ltu_false_inv in H; cleanup_repr H
         | simple apply lt_repr in H; [ | rep_omega | rep_omega]
         | simple apply lt_repr_false in H; [ | rep_omega | rep_omega]
         | simple apply lt_inv in H; cleanup_repr H
         | simple apply lt_false_inv in H; cleanup_repr H
         | idtac
         ];
    rewrite ?Byte_signed_lem, ?Byte_signed_lem',
                 ?int_repr_byte_signed_eq0, ?int_repr_byte_signed_eq0
      in H.
*)

Ltac Intro_prop ::=
  autorewrite with gather_prop;
  match goal with
   | |- semax _ ?PQR _ _ =>
       first [ is_evar PQR; fail 1
              | simple apply semax_extract_PROP; intro
              | move_from_SEP' PQR;
                simple apply semax_extract_PROP; intro
              | flatten_in_SEP PQR
              ]
   | |- _ && ?PQR |-- _ =>
       first [ is_evar PQR; fail 1
              | simple apply derives_extract_prop; intro
              | simple apply derives_extract_PROP; intro
              | move_from_SEP' PQR;
                 simple apply derives_extract_PROP; intro
              | flatten_in_SEP PQR
               ]
   | |- ?PQR |-- _ =>  (* this case is obsolete, should probably be deleted *)
       first [ is_evar PQR; fail 1
              | simple apply derives_extract_prop; intro
              | simple apply derives_extract_PROP; intro
              | move_from_SEP' PQR;
                 simple apply derives_extract_PROP; intro
              | flatten_in_SEP PQR
               ]
  end.

Lemma typed_false_of_bool : forall b,
  typed_false tint (Val.of_bool b) <-> b = false.
Proof.
  intros.
  destruct b; unfold typed_false; simpl; split; intros; congruence.
Qed.

Lemma typed_true_of_bool : forall b,
  typed_true tint (Val.of_bool b) <-> b = true.
Proof.
  intros.
  destruct b; unfold typed_true; simpl; split; intros; congruence.
Qed.

Ltac subst_eqb :=
  repeat first [
    rewrite Z.eqb_true by auto
  | rewrite Z.eqb_false by auto
  ].

Lemma body_is_leap_year: semax_body Vprog Gprog f_is_leap_year is_leap_year_spec.
Proof.
  start_function f_is_leap_year_hint.
  forwardD.
  { entailer!. inversion H0. inversion H2. }
  forwardD.
  forwardD.
  { entailer!. inversion H1. inversion H3. }
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  { entailer!. inversion H3. inversion H5. }
  { entailer!. inversion H2. inversion H4. }
  forwardD.
  - entailer!.
    unfold is_leap_year.
    autorewrite with norm in *.
    pose_rem_repable_signeds.
    do_repr_inj H0.
    apply repr_inj_signed in H1. 2, 3 : rep_omega.
    rewrite Zquot.Zrem_Zmod_zero in * by rep_omega.
    subst_eqb.
    simpl. auto.
  - entailer!.
    unfold is_leap_year.
    autorewrite with norm in H0.
    autorewrite with norm in H1.
    rewrite typed_false_of_bool in H0.
    pose_rem_repable_signeds.
    do_repr_inj H0.
    apply repr_inj_signed in H1. 2, 3 : rep_omega.
    rewrite Zquot.Zrem_Zmod_zero in * by rep_omega.
    subst_eqb.
    simpl.
    destruct (Int.eq (Int.repr (Z.rem year 400)) (Int.repr 0)) eqn:H7.
    + do_repr_inj H7.
      rewrite Zquot.Zrem_Zmod_zero in * by rep_omega.
      subst_eqb.
      simpl. auto.
    + do_repr_inj H7.
      rewrite Zquot.Zrem_Zmod_zero in * by rep_omega.
      subst_eqb.
      simpl. auto.
  - entailer!.
    unfold is_leap_year.
    autorewrite with norm in H1.
    pose_rem_repable_signeds.
    do_repr_inj H1.
    rewrite Zquot.Zrem_Zmod_zero in * by rep_omega.
    subst_eqb.
    simpl.
    destruct (Int.eq (Int.repr (Z.rem year 400)) (Int.repr 0)) eqn:H7.
    + do_repr_inj H7.
      rewrite Zquot.Zrem_Zmod_zero in * by rep_omega.
      subst_eqb.
      simpl. auto.
    + do_repr_inj H7.
      rewrite Zquot.Zrem_Zmod_zero in * by rep_omega.
      subst_eqb.
      simpl. auto.
Qed.
