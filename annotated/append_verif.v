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
match goal with
| |- ?P => let d1 := eval hnf in f_append_hint in
           change (let d := @abbreviate _ d1 in P)
end.
cbv delta [Swhile].
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
    {
      Exists a s1b t u H13. apply delta_derives_refl.
      (*  entailer!. rewrite (proj1 H4 (eq_refl _)). simpl. cancel. *)
    }
  }
  {
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    {
      Exists x.
      entailer!.
      rewrite (proj1 H16 (eq_refl _)). simpl.
      unfold listrep at 3; fold listrep. normalize.
      pull_right (listrep sh (a :: s2) t -* listrep sh ((a0 :: s1b0) ++ s2) x).
      apply modus_ponens_wand'.
      unfold listrep at 2; fold listrep. Exists y; auto.
    }
  }
Qed.

