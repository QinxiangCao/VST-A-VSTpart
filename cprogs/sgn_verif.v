Require Import cprogs.sgn_prog.
Require Import cprogs.sgn_annot.
Require Import AClight.proofauto.
Require Import AClight.advanced_forward.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Lemma body_sgn : semax_body Vprog Gprog f_sgn sgn_spec.
Proof.
start_function f_sgn_hint.
verify.
all: entailer!; do 2 f_equal; destruct x; simpl;
  try match goal with
  | H : context [Z.pos ?p] |- _ => pose proof (Pos2Z.pos_is_pos p)
  | H : context [Z.neg ?p] |- _ => pose proof (Pos2Z.neg_is_neg p)
  end;
  omega.
Qed.

(*
Lemma body_sgn : semax_body Vprog Gprog f_sgn sgn_spec.
Proof.
start_function f_sgn_hint.
forwardD.
forwardD.
forwardD.
forwardD.
forwardD.
forwardD.
forwardD.
all: entailer!; do 2 f_equal; destruct x; simpl;
  try match goal with
  | H : context [Z.pos ?p] |- _ => pose proof (Pos2Z.pos_is_pos p)
  | H : context [Z.neg ?p] |- _ => pose proof (Pos2Z.neg_is_neg p)
  end;
  omega.
Qed.
*)

