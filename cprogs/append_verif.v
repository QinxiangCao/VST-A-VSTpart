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
Require Import cprogs.append_prog.
Require Import cprogs.append_def.
Require Import cprogs.append_annot.

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
  start_function f_append_hint.
  verify.
  + rewrite listrep_null. normalize.
    Exists y.
    simpl; entailer!.
  + destruct s1 as [| a s1b]; [unfold listrep at 1; fold listrep; normalize; entailer! |].
    Exists a s1b.
    entailer!.
  + subst s1.
    unfold listrep at 1; fold listrep.
    Intros u; Exists u.
    entailer!.
  + Exists a s1b x u.
    subst s1. entailer!. simpl. cancel_wand.
  + destruct s1b as [| b s1c]; unfold listrep at 3; fold listrep; [ Intros; contradiction |].
    Intros z.
    Exists b s1c z.
    entailer!.
  + Exists b s1c u z.
    simpl app.
    entailer!.
    rewrite sepcon_comm.
    apply RAMIF_PLAIN.trans''.
    apply wand_sepcon_adjoint.
    simpl.
    forget (b::s1c++s2) as s3.
    unfold listrep; fold listrep; Exists u; auto.
  + Exists x.
    entailer!.
    rewrite (proj1 H4 (eq_refl _)). simpl.
    unfold listrep at 3; fold listrep.
    normalize.
    pull_right (listrep sh (a0 :: s2) t -* listrep sh ((a :: s1b) ++ s2) x).
    apply modus_ponens_wand'.
    unfold listrep at 2; fold listrep. Exists y; auto.
Qed.
Lemma body_append_long: semax_body Vprog Gprog f_append append_spec.
Proof.
start_function f_append_hint.
forwardD.
* forwardD.
  {
    rewrite listrep_null. normalize.
    Exists y.
    simpl; entailer!.
  }
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
  forwardD.
  {
    Exists a s1b x u.
    subst s1. entailer!. simpl. cancel_wand.
  }
  {
    (* Intro EXs *)
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
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
  }
  { forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    {
      Exists x.
      entailer!.
      rewrite (proj1 H4 (eq_refl _)). simpl.
      unfold listrep at 3; fold listrep.
      normalize.
      pull_right (listrep sh (a0 :: s2) t -* listrep sh ((a :: s1b) ++ s2) x).
      apply modus_ponens_wand'.
      unfold listrep at 2; fold listrep. Exists y; auto.
    }
  }
Qed.

