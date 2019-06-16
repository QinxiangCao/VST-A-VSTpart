(************************************************************)
(************************************************************)
(**                                                        **)
(**                                                        **)
(**      Definitions and tactics for decorated program.    **)
(**                                                        **)
(**                                                        **)
(************************************************************)
(************************************************************)


Require Import annotation_proofauto.
Require Import append.
Require Import append_def.
Require Import append_annotation.

(************************************************************)
(************************************************************)
(**                                                        **)
(**                                                        **)
(**                       THE  PROOF                       **)
(**                                                        **)
(**                                                        **)
(************************************************************)
(************************************************************)

Lemma body_append: semax_body Vprog Gprog f_append append_spec.
Proof.
start_function.
use_annotation f_append_hint.
forwardD sh.
forwardD s1.
forwardD s2.
forwardD x.
forwardD y.
forwardD.
* forwardD.
  rewrite listrep_null. normalize.
  Exists y.
  simpl; entailer!.
* forwardD.
  forwardD.
  {
    destruct s1 as [| a s1b]; [unfold listrep at 1; fold listrep; normalize; entailer! |].
    Exists a s1b.
    entailer!.
  }
  forwardD.
  forwardD.
  forwardD.
  {
    subst s1.
    unfold listrep at 1; fold listrep.
    Intros u; Exists u.
    entailer!.
  }
  forwardD.
  forwardD.
  forwardD.
  {
    Exists a s1b x u.
    subst s1. entailer!. simpl. cancel_wand.
  }
  {
    (* clear a s1b H0 u. *) (* Without clearing deadvars here, we will have "a is already used later" *)
    (* Intro EXs *)
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    (* forward_if *)
    forwardD.
    (* then branch *)
    forwardD.
    {
      destruct s1b as [| b s1c]; unfold listrep at 3; fold listrep; [ Intros; contradiction |].
      Intros z.
      Exists b s1c z.
      entailer!.
    }
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    {
      Exists b s1c u z.
      simpl app.
      entailer!.
      rewrite sepcon_comm.
      apply RAMIF_PLAIN.trans''.
      apply wand_sepcon_adjoint.
      simpl.
      forget (b::s1c++s2) as s3.
      unfold listrep; fold listrep; Exists u; auto.
    }
    (* else branch *)
    forwardD.
    forwardD.
  (* lazymatch goal with
  (* entailment *)
  | |- let d := @abbreviate _ _ in ENTAIL _, _ |-- ?Post =>
      intro d; clear d;
      is_evar Post;
        repeat first
        [ apply delta_derives_refl; fail 2
        | match reverse goal with
          | H : Intro_tag ?x |- _ =>
            Exists x; clear H; idtac x
          end
        ]end. *)
    (* 
    Lemma revert_evar : forall {A} (x : A) P (Q : assert),
      EX x, P x |-- Q -> P x |-- Q.
    Proof.
      intros. eapply derives_trans. 2 : apply H. EExists. apply derives_refl.
    Qed.
    Lemma delta_remove : forall Delta P Q,
      P |-- Q -> ENTAIL Delta, P |-- Q.
    Proof.
      intros. apply andp_left2. assumption.
    Qed.
    apply delta_remove.
    match goal with
    | |- ?P |-- ?Q =>
      match P with
      | ?P' u => idtac P'
      end
    end.
    eapply (revert_evar u).
    eapply exp_right with t.
    Exists u. Exists u. simpl in Post. Exists t. Exists s1b. Exists a. apply delta_derives_refl. *)
    (* match goal with
          | H : Intros_tag ?x |- _ =>
            idtac x; Exists x
          end.
          match goal with
          | H : Intros_tag ?x |- _ =>
            idtac x; Exists x
          end.
          Exists t.
          match goal with
          | H : Intros_tag ?x |- _ =>
            idtac x; Exists x
          end.
    {
      Exists u. Exists t.
      Exists a. Exists s1b. Exists t. u H13. apply delta_derives_refl.
      (*  entailer!. rewrite (proj1 H4 (eq_refl _)). simpl. cancel. *)
    } *)
  }
  { forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    {
      Exists x.
      entailer!.
      rewrite (proj1 H9 (eq_refl _)). simpl.
      unfold listrep at 3; fold listrep. normalize.
      pull_right (listrep sh (a :: s2) t -* listrep sh ((a0 :: s1b0) ++ s2) x).
      apply modus_ponens_wand'.
      unfold listrep at 2; fold listrep. Exists y; auto.
    }
  }
Qed.

