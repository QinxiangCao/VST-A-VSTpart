(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for constant propagation (processor-dependent part). *)

Require Import Coqlib.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import ConstpropOp.
Require Import Constprop.

(** * Correctness of the static analysis *)

Section ANALYSIS.

Variable ge: genv.
Variable sp: val.

(** We first show that the dataflow analysis is correct with respect
  to the dynamic semantics: the approximations (sets of values) 
  of a register at a program point predicted by the static analysis
  are a superset of the values actually encountered during concrete
  executions.  We formalize this correspondence between run-time values and
  compile-time approximations by the following predicate. *)

Definition val_match_approx (a: approx) (v: val) : Prop :=
  match a with
  | Unknown => True
  | I p => v = Vint p
  | F p => v = Vfloat p
  | G symb ofs => v = symbol_address ge symb ofs
  | S ofs => v = Val.add sp (Vint ofs)
  | _ => False
  end.

Inductive val_list_match_approx: list approx -> list val -> Prop :=
  | vlma_nil:
      val_list_match_approx nil nil
  | vlma_cons:
      forall a al v vl,
      val_match_approx a v ->
      val_list_match_approx al vl ->
      val_list_match_approx (a :: al) (v :: vl).

Ltac SimplVMA :=
  match goal with
  | H: (val_match_approx (I _) ?v) |- _ =>
      simpl in H; (try subst v); SimplVMA
  | H: (val_match_approx (F _) ?v) |- _ =>
      simpl in H; (try subst v); SimplVMA
  | H: (val_match_approx (G _ _) ?v) |- _ =>
      simpl in H; (try subst v); SimplVMA
  | H: (val_match_approx (S _) ?v) |- _ =>
      simpl in H; (try subst v); SimplVMA
  | _ =>
      idtac
  end.

Ltac InvVLMA :=
  match goal with
  | H: (val_list_match_approx nil ?vl) |- _ =>
      inv H
  | H: (val_list_match_approx (?a :: ?al) ?vl) |- _ =>
      inv H; SimplVMA; InvVLMA
  | _ =>
      idtac
  end.

(** We then show that [eval_static_operation] is a correct abstract
  interpretations of [eval_operation]: if the concrete arguments match
  the given approximations, the concrete results match the
  approximations returned by [eval_static_operation]. *)

Lemma eval_static_condition_correct:
  forall cond al vl m b,
  val_list_match_approx al vl ->
  eval_static_condition cond al = Some b ->
  eval_condition cond vl m = Some b.
Proof.
  intros until b.
  unfold eval_static_condition. 
  case (eval_static_condition_match cond al); intros;
  InvVLMA; simpl; congruence.
Qed.

Remark shift_symbol_address:
  forall symb ofs n,
  symbol_address ge symb (Int.add ofs n) = Val.add (symbol_address ge symb ofs) (Vint n).
Proof.
  unfold symbol_address; intros. destruct (Genv.find_symbol ge symb); auto. 
Qed.

Lemma eval_static_addressing_correct:
  forall addr al vl v,
  val_list_match_approx al vl ->
  eval_addressing ge sp addr vl = Some v ->
  val_match_approx (eval_static_addressing addr al) v.
Proof.
  intros until v. unfold eval_static_addressing.
  case (eval_static_addressing_match addr al); intros;
  InvVLMA; simpl in *; FuncInv; try subst v; auto.
  rewrite shift_symbol_address; auto.
  rewrite Val.add_assoc. auto.
  repeat rewrite shift_symbol_address. auto.
  fold (Val.add (Vint n1) (symbol_address ge id ofs)).
  repeat rewrite shift_symbol_address. repeat rewrite Val.add_assoc. rewrite Val.add_permut. auto.
  repeat rewrite Val.add_assoc. decEq; simpl. rewrite Int.add_assoc. auto.
  fold (Val.add (Vint n1) (Val.add sp (Vint ofs))).
  rewrite Val.add_assoc. rewrite Val.add_permut. rewrite Val.add_assoc. 
  simpl. rewrite Int.add_assoc; auto.
  rewrite shift_symbol_address. auto.
  rewrite Val.add_assoc. auto. 
  rewrite shift_symbol_address. auto.
  rewrite shift_symbol_address. rewrite Int.mul_commut; auto. 
Qed.

Lemma eval_static_operation_correct:
  forall op al vl m v,
  val_list_match_approx al vl ->
  eval_operation ge sp op vl m = Some v ->
  val_match_approx (eval_static_operation op al) v.
Proof.
  intros until v.
  unfold eval_static_operation. 
  case (eval_static_operation_match op al); intros;
  InvVLMA; simpl in *; FuncInv; try subst v; auto.
  destruct (propagate_float_constants tt); simpl; auto.
  rewrite Int.sub_add_opp. rewrite shift_symbol_address. rewrite Val.sub_add_opp. auto.
  destruct (Int.eq n2 Int.zero). inv H0. 
    destruct (Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); inv H0; simpl; auto.
  destruct (Int.eq n2 Int.zero); inv H0; simpl; auto.
  destruct (Int.eq n2 Int.zero). inv H0. 
    destruct (Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); inv H0; simpl; auto.
  destruct (Int.eq n2 Int.zero); inv H0; simpl; auto.
  destruct (Int.ltu n2 Int.iwordsize); simpl; auto.
  destruct (Int.ltu n Int.iwordsize); simpl; auto.
  destruct (Int.ltu n2 Int.iwordsize); simpl; auto.
  destruct (Int.ltu n Int.iwordsize); simpl; auto.
  destruct (Int.ltu n (Int.repr 31)); inv H0. simpl; auto.
  destruct (Int.ltu n2 Int.iwordsize); simpl; auto.
  destruct (Int.ltu n Int.iwordsize); simpl; auto.
  destruct (Int.ltu n Int.iwordsize); simpl; auto.
  eapply eval_static_addressing_correct; eauto.
  unfold eval_static_intoffloat.
  destruct (Float.intoffloat n1) as []_eqn; simpl in H0; inv H0.
  simpl; auto.
  destruct (propagate_float_constants tt); simpl; auto.
  unfold eval_static_condition_val. destruct (eval_static_condition c vl0) as [b|]_eqn.
  rewrite (eval_static_condition_correct _ _ _ m _ H Heqo). 
  destruct b; simpl; auto.
  simpl; auto.
Qed.

(** * Correctness of strength reduction *)

(** We now show that strength reduction over operators and addressing
  modes preserve semantics: the strength-reduced operations and
  addressings evaluate to the same values as the original ones if the
  actual arguments match the static approximations used for strength
  reduction. *)

Section STRENGTH_REDUCTION.

Variable app: D.t.
Variable rs: regset.
Variable m: mem.
Hypothesis MATCH: forall r, val_match_approx (approx_reg app r) rs#r.

Ltac InvApproxRegs :=
  match goal with
  | [ H: _ :: _ = _ :: _ |- _ ] => 
        injection H; clear H; intros; InvApproxRegs
  | [ H: ?v = approx_reg app ?r |- _ ] => 
        generalize (MATCH r); rewrite <- H; clear H; intro; InvApproxRegs
  | _ => idtac
  end.

Lemma cond_strength_reduction_correct:
  forall cond args vl,
  vl = approx_regs app args ->
  let (cond', args') := cond_strength_reduction cond args vl in
  eval_condition cond' rs##args' m = eval_condition cond rs##args m.
Proof.
  intros until vl. unfold cond_strength_reduction.
  case (cond_strength_reduction_match cond args vl); simpl; intros; InvApproxRegs; SimplVMA.
  rewrite H0. apply Val.swap_cmp_bool. 
  rewrite H. auto.
  rewrite H0. apply Val.swap_cmpu_bool.
  rewrite H. auto.
  auto.
Qed.

Lemma addr_strength_reduction_correct:
  forall addr args vl,
  vl = approx_regs app args ->
  let (addr', args') := addr_strength_reduction addr args vl in
  eval_addressing ge sp addr' rs##args' = eval_addressing ge sp addr rs##args.
Proof.
  intros until vl. unfold addr_strength_reduction.
  destruct (addr_strength_reduction_match addr args vl); simpl; intros; InvApproxRegs; SimplVMA.
  rewrite shift_symbol_address; congruence.
  rewrite H. rewrite Val.add_assoc; auto.
  rewrite H; rewrite H0. repeat rewrite shift_symbol_address. auto.
  rewrite H; rewrite H0. rewrite Int.add_assoc. rewrite Int.add_permut. repeat rewrite shift_symbol_address.
  rewrite Val.add_assoc. rewrite Val.add_permut. auto.
  rewrite H; rewrite H0. repeat rewrite Val.add_assoc. rewrite Int.add_assoc. auto.
  rewrite H; rewrite H0. repeat rewrite Val.add_assoc. rewrite Val.add_permut. 
  rewrite Int.add_assoc. auto.
  rewrite H0. rewrite shift_symbol_address. repeat rewrite Val.add_assoc. 
  decEq; decEq. apply Val.add_commut.
  rewrite H. rewrite shift_symbol_address. repeat rewrite Val.add_assoc.
  rewrite (Val.add_permut (rs#r1)). decEq; decEq. apply Val.add_commut.
  rewrite H0. rewrite Val.add_assoc. rewrite Val.add_permut. auto.
  rewrite H. rewrite Val.add_assoc. auto.
  rewrite H; rewrite H0. rewrite Int.add_assoc. repeat rewrite shift_symbol_address. auto.
  rewrite H0. rewrite shift_symbol_address. rewrite Val.add_assoc. decEq; decEq. apply Val.add_commut.
  rewrite H. auto.
  rewrite H. rewrite shift_symbol_address. auto.
  rewrite H. rewrite shift_symbol_address. rewrite Int.mul_commut; auto.
  auto.
Qed.

Lemma make_addimm_correct:
  forall n r,
  let (op, args) := make_addimm n r in
  exists v, eval_operation ge sp op rs##args m = Some v /\ Val.lessdef (Val.add rs#r (Vint n)) v.
Proof.
  intros. unfold make_addimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. 
  subst. exists (rs#r); split; auto. destruct (rs#r); simpl; auto; rewrite Int.add_zero; auto.
  exists (Val.add rs#r (Vint n)); auto.
Qed.
  
Lemma make_shlimm_correct:
  forall n r1,
  let (op, args) := make_shlimm n r1 in
  exists v, eval_operation ge sp op rs##args m = Some v /\ Val.lessdef (Val.shl rs#r1 (Vint n)) v.
Proof.
  intros; unfold make_shlimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (rs#r1); split; auto. destruct (rs#r1); simpl; auto. rewrite Int.shl_zero. auto.
  econstructor; split. simpl. eauto. auto.
Qed.

Lemma make_shrimm_correct:
  forall n r1,
  let (op, args) := make_shrimm n r1 in
  exists v, eval_operation ge sp op rs##args m = Some v /\ Val.lessdef (Val.shr rs#r1 (Vint n)) v.
Proof.
  intros; unfold make_shrimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (rs#r1); split; auto. destruct (rs#r1); simpl; auto. rewrite Int.shr_zero. auto.
  econstructor; split; eauto. simpl. auto.
Qed.

Lemma make_shruimm_correct:
  forall n r1,
  let (op, args) := make_shruimm n r1 in
  exists v, eval_operation ge sp op rs##args m = Some v /\ Val.lessdef (Val.shru rs#r1 (Vint n)) v.
Proof.
  intros; unfold make_shruimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (rs#r1); split; auto. destruct (rs#r1); simpl; auto. rewrite Int.shru_zero. auto.
  econstructor; split; eauto. simpl. congruence.
Qed.

Lemma make_mulimm_correct:
  forall n r1,
  let (op, args) := make_mulimm n r1 in
  exists v, eval_operation ge sp op rs##args m = Some v /\ Val.lessdef (Val.mul rs#r1 (Vint n)) v.
Proof.
  intros; unfold make_mulimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (Vint Int.zero); split; auto. destruct (rs#r1); simpl; auto. rewrite Int.mul_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.one; intros. subst.
  exists (rs#r1); split; auto. destruct (rs#r1); simpl; auto. rewrite Int.mul_one; auto.
  destruct (Int.is_power2 n) as []_eqn; intros.
  rewrite (Val.mul_pow2 rs#r1 _ _ Heqo). apply make_shlimm_correct; auto. 
  econstructor; split; eauto. auto. 
Qed.

Lemma make_divimm_correct:
  forall n r1 r2 v,
  Val.divs rs#r1 rs#r2 = Some v ->
  rs#r2 = Vint n ->
  let (op, args) := make_divimm n r1 r2 in
  exists w, eval_operation ge sp op rs##args m = Some w /\ Val.lessdef v w.
Proof.
  intros; unfold make_divimm.
  destruct (Int.is_power2 n) as []_eqn.
  destruct (Int.ltu i (Int.repr 31)) as []_eqn.
  exists v; split; auto. simpl. eapply Val.divs_pow2; eauto. congruence. 
  exists v; auto.
  exists v; auto.
Qed.

Lemma make_divuimm_correct:
  forall n r1 r2 v,
  Val.divu rs#r1 rs#r2 = Some v ->
  rs#r2 = Vint n ->
  let (op, args) := make_divuimm n r1 r2 in
  exists w, eval_operation ge sp op rs##args m = Some w /\ Val.lessdef v w.
Proof.
  intros; unfold make_divuimm.
  destruct (Int.is_power2 n) as []_eqn.
  replace v with (Val.shru rs#r1 (Vint i)). 
  eapply make_shruimm_correct; eauto.
  eapply Val.divu_pow2; eauto. congruence.
  exists v; auto.
Qed.

Lemma make_moduimm_correct:
  forall n r1 r2 v,
  Val.modu rs#r1 rs#r2 = Some v ->
  rs#r2 = Vint n ->
  let (op, args) := make_moduimm n r1 r2 in
  exists w, eval_operation ge sp op rs##args m = Some w /\ Val.lessdef v w.
Proof.
  intros; unfold make_moduimm.
  destruct (Int.is_power2 n) as []_eqn.
  exists v; split; auto. simpl. decEq. eapply Val.modu_pow2; eauto. congruence.
  exists v; auto.
Qed.

Lemma make_andimm_correct:
  forall n r,
  let (op, args) := make_andimm n r in
  exists v, eval_operation ge sp op rs##args m = Some v /\ Val.lessdef (Val.and rs#r (Vint n)) v.
Proof.
  intros; unfold make_andimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst n. exists (Vint Int.zero); split; auto. destruct (rs#r); simpl; auto. rewrite Int.and_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.mone; intros.
  subst n. exists (rs#r); split; auto. destruct (rs#r); simpl; auto. rewrite Int.and_mone; auto.
  econstructor; split; eauto. auto. 
Qed.

Lemma make_orimm_correct:
  forall n r,
  let (op, args) := make_orimm n r in
  exists v, eval_operation ge sp op rs##args m = Some v /\ Val.lessdef (Val.or rs#r (Vint n)) v.
Proof.
  intros; unfold make_orimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst n. exists (rs#r); split; auto. destruct (rs#r); simpl; auto. rewrite Int.or_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.mone; intros.
  subst n. exists (Vint Int.mone); split; auto. destruct (rs#r); simpl; auto. rewrite Int.or_mone; auto.
  econstructor; split; eauto. auto. 
Qed.

Lemma make_xorimm_correct:
  forall n r,
  let (op, args) := make_xorimm n r in
  exists v, eval_operation ge sp op rs##args m = Some v /\ Val.lessdef (Val.xor rs#r (Vint n)) v.
Proof.
  intros; unfold make_xorimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst n. exists (rs#r); split; auto. destruct (rs#r); simpl; auto. rewrite Int.xor_zero; auto.
  econstructor; split; eauto. auto. 
Qed.

Lemma op_strength_reduction_correct:
  forall op args vl v,
  vl = approx_regs app args ->
  eval_operation ge sp op rs##args m = Some v ->
  let (op', args') := op_strength_reduction op args vl in
  exists w, eval_operation ge sp op' rs##args' m = Some w /\ Val.lessdef v w.
Proof.
  intros until v; unfold op_strength_reduction;
  case (op_strength_reduction_match op args vl); simpl; intros.
(* sub *)
  InvApproxRegs. SimplVMA. inv H0; rewrite H. rewrite Val.sub_add_opp. apply make_addimm_correct; auto. 
(* mul *)
  InvApproxRegs. SimplVMA. inv H0; rewrite H. apply make_mulimm_correct; auto.
(* divs *) 
  assert (rs#r2 = Vint n2). clear H0. InvApproxRegs; SimplVMA; auto.
  apply make_divimm_correct; auto.
(* divu *) 
  assert (rs#r2 = Vint n2). clear H0. InvApproxRegs; SimplVMA; auto.
  apply make_divuimm_correct; auto.
(* modu *) 
  assert (rs#r2 = Vint n2). clear H0. InvApproxRegs; SimplVMA; auto.
  apply make_moduimm_correct; auto.
(* and *)
  InvApproxRegs. SimplVMA. inv H0; rewrite H. apply make_andimm_correct; auto.
(* or *)
  InvApproxRegs. SimplVMA. inv H0; rewrite H. apply make_orimm_correct; auto.
(* xor *)
  InvApproxRegs. SimplVMA. inv H0; rewrite H. apply make_xorimm_correct; auto.
(* shl *)
  InvApproxRegs. SimplVMA. inv H0; rewrite H. apply make_shlimm_correct; auto.
(* shr *)
  InvApproxRegs. SimplVMA. inv H0; rewrite H. apply make_shrimm_correct; auto.
(* shru *)
  InvApproxRegs. SimplVMA. inv H0; rewrite H. apply make_shruimm_correct; auto.
(* lea *)
  generalize (addr_strength_reduction_correct addr args0 vl0 H). 
  destruct (addr_strength_reduction addr args0 vl0) as [addr' args'].
  intro EQ. exists v; split; auto. simpl. congruence.
(* cond *)
  generalize (cond_strength_reduction_correct c args0 vl0 H). 
  destruct (cond_strength_reduction c args0 vl0) as [c' args']; intros.
  rewrite <- H1 in H0; auto. econstructor; split; eauto.
(* default *)
  exists v; auto.
Qed.

Lemma builtin_strength_reduction_correct:
  forall ef args vl m t vres m',
  vl = approx_regs app args ->
  external_call ef ge rs##args m t vres m' ->
  let (ef', args') := builtin_strength_reduction ef args vl in
  external_call ef' ge rs##args' m t vres m'.
Proof.
  intros until m'. unfold builtin_strength_reduction.
  destruct (builtin_strength_reduction_match ef args vl); simpl; intros; InvApproxRegs; SimplVMA.
  unfold symbol_address in H. destruct (Genv.find_symbol ge symb) as [b|]_eqn; rewrite H in H0.
  rewrite volatile_load_global_charact. exists b; auto. 
  inv H0.
  unfold symbol_address in H1. destruct (Genv.find_symbol ge symb) as [b|]_eqn; rewrite H1 in H0.
  rewrite volatile_store_global_charact. exists b; auto. 
  inv H0.
  auto.
Qed.

End STRENGTH_REDUCTION.

End ANALYSIS.

