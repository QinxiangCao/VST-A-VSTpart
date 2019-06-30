(************************************************************)
(************************************************************)
(**                                                        **)
(**                                                        **)
(**      Definitions and tactics for decorated program.    **)
(**                                                        **)
(**                                                        **)
(************************************************************)
(************************************************************)


Require Import Annot.annotation_proofauto.
Require Import Annot.reverse.
Require Import Annot.reverse_def.
Require Import Annot.reverse_annotation.

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
forwardD.
forwardD.
forwardD.
{
  Exists nullval p (@nil val) l.
  entailer!.
  unfold listrep.
  entailer!.
}
{
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  {
    forwardD.
    {
      destruct l2 as [| x l2'].
      { entailer!. pose proof proj2 H7 eq_refl. subst. tauto. }
      unfold listrep at 2; fold listrep.
      Intros t.
      Exists t x l2'.
      entailer!.
    }
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    Exists v t (x :: l1) l2'.
    entailer!.
    + simpl. rewrite app_ass. auto.
    + unfold listrep at 2; fold listrep.
      Exists w. entailer!.
  }
  forwardD.
Abort.
