Require Import VST.floyd.proofauto.
Require Import AClight.ramification.

Fixpoint fold_Ssequence (sl: list statement) : statement :=
  match sl with
  | [] => Sskip
  | [s] => s
  | s :: sl => Ssequence s (fold_Ssequence sl)
  end.

Ltac split_by_number s n :=
  let sl := eval cbv [unfold_Ssequence] in (unfold_Ssequence s) in
  let s' := eval cbv [fold_Ssequence firstn skipn app] in
  (Ssequence
    (fold_Ssequence (firstn n sl))
    (fold_Ssequence (skipn n sl))) in
  s'.

Ltac split_semax_statement n :=
  match goal with
  | |- semax ?Delta ?P ?c ?Q =>
      let c' := split_by_number c n in
      apply semax_unfold_Ssequence with c';
      [reflexivity | ]
  end.

Ltac localize n L G' :=
  split_semax_statement n;
  eapply semax_ramification_P;
  swap 1 2.

Lemma exp_wand : forall T (P : T -> mpred) Q,
  ALL x, P x -* Q |-- (EX x, P x) -* Q.
Proof.
  intros.
  apply wand_sepcon_adjoint. Intros x. sep_eapply allp_instantiate'.
  apply wand_frame_elim''.
Qed.

Lemma wand_exp : forall T P (Q : T -> mpred),
  EX x, P -* Q x |-- P -* (EX x, Q x).
Proof.
  intros. Intros x.
  apply wand_sepcon_adjoint. EExists.
  apply wand_frame_elim''.
Qed.

Lemma exp_wand_exp : forall T1 T2 (P : T1 -> mpred) (Q : T2 -> mpred),
  ALL x, EX y, P x -* Q y |-- (EX x, P x) -* (EX y, Q y).
Proof.
  intros.
  eapply derives_trans. 2 : apply exp_wand.
  apply allp_derives. intros.
  eapply derives_trans. 2 : apply wand_exp.
  auto.
Qed.

