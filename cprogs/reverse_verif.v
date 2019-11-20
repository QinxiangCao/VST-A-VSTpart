(************************************************************)
(************************************************************)
(**                                                        **)
(**                                                        **)
(**      Definitions and tactics for decorated program.    **)
(**                                                        **)
(**                                                        **)
(************************************************************)
(************************************************************)


Require Import AClight.proofauto.
Require Import cprogs.reverse_prog.
Require Import cprogs.reverse_def.
Require Import cprogs.reverse_annot.

(************************************************************)
(************************************************************)
(**                                                        **)
(**                                                        **)
(**                       THE  PROOF                       **)
(**                                                        **)
(**                                                        **)
(************************************************************)
(************************************************************)

Lemma body_reverse: semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
start_function f_reverse_hint.
verify.
+ listrep_entailer.         
+  listrep_entailer.
+ listrep_entailer.
  subst; simpl. rewrite app_ass. auto. 
+ listrep_entailer.
  subst l2; rewrite <- app_nil_end, rev_involutive. auto.
Qed.

Lemma body_reverse_long: semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
start_function f_reverse_hint.
forwardD.
forwardD.
forwardD.
forwardD.
{
  listrep_entailer.
}
{
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  {
    forwardD.
  }
  {
    forwardD.
  }
  forwardD.
  {
    Intros. listrep_entailer.
  }
  {
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    listrep_entailer.
    subst; simpl. rewrite app_ass. auto.
  }
}
forwardD.
forwardD.
listrep_entailer.
subst l2.
rewrite <- app_nil_end, rev_involutive.
auto.
Qed.

