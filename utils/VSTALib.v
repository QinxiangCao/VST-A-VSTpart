From Coq Require Export String List ZArith Lia.
From compcert Require Export Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require VST.floyd.proofauto.
Require Export Csplit.semantics.
Require Export utils.AClightNotations.
Require Export Csplit.strong.
Require Export FloydSeq.client_lemmas.
Require Export Csplit.strongSoundness.
Require Export Csplit.AClightFunc.
Require Export FloydSeq.proofauto. Export strong(semax).
Open Scope Z_scope.
Export AClightNotations.

Ltac cleanup_no_post_exists ::=
 (match goal with |-  context[eq_no_post] =>
  let vret := fresh "vret" in let H := fresh in
  apply extract_exists_pre; intro vret;
  apply semax_extract_PROP; intro H;
  change (eq_no_post vret) with (eq vret) in H;
  subst vret
 end
  || unfold eq_no_post);
  try abbreviate_semax.

Ltac VSTA_abbreviate_semax_pre :=
  match goal with
  | |- strong.semax _ _ ?c _ =>
         is_var c; unfold c, abbreviate
  | _ => idtac
  end;
  match goal with
  | |- strong.semax _ _ (Sreturn _) ?P =>
         is_var P; unfold P, abbreviate
  | |- strong.semax _ _ (Ssequence (Sreturn _)) ?P =>
         is_var P; unfold P, abbreviate
  | _ => idtac
  end;
  match goal with
  | |- strong.semax _ _ (Sreturn _) (return_split_assert _) =>
         apply semax_return_return_split_assert
  | |- strong.semax _ _ (Ssequence (Sreturn _)) (return_split_assert _) =>
         apply semax_return_return_split_assert
  | |- context [ RA_normal (normal_split_assert _) ] =>
         unfold RA_normal, normal_split_assert
  | _ => idtac
  end.

Ltac VSTA_abbreviate_semax_post :=
  FloydSeq.semax_tactics.abbreviate_semax;
  match goal with
  | |- strong.semax _ _ ?c _ =>
         is_var c; unfold c, abbreviate
  | |- context [ RA_normal (normal_split_assert _) ] =>
         unfold RA_normal, normal_split_assert
  | _ => idtac
  end.

Ltac forward_break_branch :=
  match goal with
  | |- strong.semax _ _ (Ssequence Sbreak _) _ =>
         forward; apply TT_right
  | |- strong.semax _ _ Sbreak _ =>
         forward; apply TT_right
  | _ => idtac
  end.

Ltac forward :=
  VSTA_abbreviate_semax_pre;
  first
    [ forward_if; forward_break_branch
    | FloydSeq.forward.forward];
  VSTA_abbreviate_semax_post.

(*
Ltac simpl_const i :=
  let i' := eval vm_compute in i in
  change i with i' in *.

Ltac rep_lia :=
  simpl_const Int.max_signed;
  simpl_const Int.min_signed;
  simpl_const Int.max_unsigned;
  simpl_const Int.half_modulus;
  simpl_const Int.modulus;
  simpl_const Int.wordsize;
  simpl_const Int64.max_signed;
  simpl_const Int64.min_signed;
  simpl_const Int64.max_unsigned;
  simpl_const Int64.half_modulus;
  simpl_const Int64.modulus;
  simpl_const Int64.wordsize;
  simpl_const (Int.signed Int.zero);
  simpl_const (Int.unsigned Int.zero);
  simpl_const (Int64.signed Int64.zero);
  simpl_const (Int64.unsigned Int64.zero);
  lia.
*)
Ltac rep_lia := rep_omega.

Tactic Notation "forward_call" constr(witness) :=
  fwd_call_dep (@nil Type) funspec_sub_refl witness;
  try VSTA_abbreviate_semax_post.

Ltac field_address_solver :=
  match goal with
  | |- @eq val ?p (field_address _ _ ?p) => idtac
  | |- @eq val (offset_val _ ?p) (field_address _ _ ?p) => idtac
  | |- @eq val (field_address _ _ ?p) ?p => idtac
  | |- @eq val (field_address _ _ ?p) (offset_val _ ?p) => idtac
  | _ => fail 1 "The proof goal is not in a form of (p = field_address _ _ p) or (offset_val _ p = field_address _ _ p)"
  end;
  unfold field_address; simpl;
  (rewrite if_true by auto with field_compatible || fail 1 "Not enough field_compatible information to derive the equality.");
  rewrite ? isptr_offset_val_zero; auto.

