From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import CSplit.AClightFunc.
Require Import CSplit.semanticsFunc.
Require Import utils.AClightNotations.
Require Import FloydSeq.proofauto.
Require Import FloydSeq.client_lemmas.
Require VST.floyd.proofauto.
Require Import FloydSeq.proofauto.
Require Import CSplit.strong.
Require Import CSplit.strongSoundness.
Require Import CSplit.soundness.

Local Open Scope Z_scope.
Import AClightNotations.

Module Info.
  Definition version := "3.6"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "macosx"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "testprogs/reverse_noinv.c"%string.
  Definition normalized := true.
End Info.

Require Import cprogs.reverse_prog.
Require Import cprogs.reverse_def.

Definition f_reverse_spec_annotation :=
  ANNOTATION_WITH  sh p l, ((
            PROP  (writable_share sh)
	    LOCAL (temp _p p)
	    SEP   (listrep sh l p)),
  (
          EX q: val,
	    PROP  ()
	    LOCAL (temp ret_temp q)
	    SEP   (listrep sh (rev l) q))).

Definition f_reverse_spec_complex :=
  ltac:(uncurry_funcspec f_reverse_spec_annotation).

Definition f_reverse_funsig: funsig :=
  (((_p, (tptr (Tstruct _list noattr))) :: nil),
   (tptr (Tstruct _list noattr))).

Definition reverse_spec :=
  ltac:(make_funcspec _reverse f_reverse_funsig f_reverse_spec_complex).

Definition f_reverse_hint :=
(EXGIVEN l
  [[(EX p sh, 
            PROP  (writable_share sh)
	    LOCAL (temp _p p)
	    SEP   (listrep sh l p))]] 
  (EXGIVEN p
    [[(EX sh, 
            PROP  (writable_share sh)
	    LOCAL (temp _p p)
	    SEP   (listrep sh l p))]] 
    (EXGIVEN sh
      [[(
            PROP  (writable_share sh)
	    LOCAL (temp _p p)
	    SEP   (listrep sh l p))]] 
      (Csequence
        (Csequence
          (Cset _w (Econst_int (Int.repr 0) tint))
          (Csequence
            (Cset _v (Etempvar _p (tptr (Tstruct _list noattr))))
            (Csequence
              (Cloop
                (Csequence
                  (Cassert (
       (EX w v l1 l2,
          PROP  (l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert))
                  (EXGIVEN w
                    [[((EX v l1 l2,
          PROP  (l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert)]] 
                    (EXGIVEN v
                      [[((EX l1 l2,
          PROP  (l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert)]] 
                      (EXGIVEN l1
                        [[((EX l2,
          PROP  (l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert)]] 
                        (EXGIVEN l2
                          [[((PROP  (l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert)]] 
                          (Csequence
                            (Cifthenelse (Etempvar _v (tptr (Tstruct _list noattr)))
                              Cskip
                              (Csequence Cbreak Cskip))
                            (Csequence
                              (Cassert (
         (EX t x l2',
	    PROP  (l = rev l1 ++ l2; l2 = x :: l2'; writable_share sh)
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert))
                              (EXGIVEN t
                                [[((EX x l2',
	    PROP  (l = rev l1 ++ l2; l2 = x :: l2'; writable_share sh)
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert)]] 
                                (EXGIVEN x
                                  [[((EX l2',
	    PROP  (l = rev l1 ++ l2; l2 = x :: l2'; writable_share sh)
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert)]] 
                                  (EXGIVEN l2'
                                    [[((PROP  (l = rev l1 ++ l2; l2 = x :: l2'; writable_share sh)
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert)]] 
                                    (Csequence
                                      (Cset _t
                                        (Efield
                                          (Ederef
                                            (Etempvar _v (tptr (Tstruct _list noattr)))
                                            (Tstruct _list noattr)) _tail
                                          (tptr (Tstruct _list noattr))))
                                      (Csequence
                                        (Cassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _v (tptr (Tstruct _list noattr)))
                                              (Tstruct _list noattr)) _tail
                                            (tptr (Tstruct _list noattr)))
                                          (Etempvar _w (tptr (Tstruct _list noattr))))
                                        (Csequence
                                          (Cset _w
                                            (Etempvar _v (tptr (Tstruct _list noattr))))
                                          (Csequence
                                            (Cset _v
                                              (Etempvar _t (tptr (Tstruct _list noattr))))
                                            Cskip))))))))))))))
                Cskip)
              (Csequence
                (Creturn (Some (Etempvar _w (tptr (Tstruct _list noattr)))))
                Cskip))))
        (Cassert (
          EX q: val,
	    PROP  ()
	    LOCAL (temp ret_temp q)
	    SEP   (listrep sh (rev l) q))))))).

Definition Gprog : funspecs :=
  ltac:(with_library prog [reverse_spec]).

Time Definition f_reverse_hint_split :=
  ltac:(compute_split f_reverse_hint).

Fixpoint remove_skip (c: statement): statement :=
  match c with
  | Clight.Ssequence c1 c2 =>
      match remove_skip c1 with
      | Clight.Sskip => remove_skip c2
      | _ => match remove_skip c2 with
             | Clight.Sskip => remove_skip c1
             | _ => Clight.Ssequence (remove_skip c1) (remove_skip c2)
             end
      end
  | Clight.Sifthenelse e c1 c2 =>
      Clight.Sifthenelse e (remove_skip c1) (remove_skip c2)
  | Clight.Sloop c1 c2 =>
      Clight.Sloop (remove_skip c1) (remove_skip c2)
  | _ =>
      c
  end.

Theorem semax_remove_skip: forall {Ora: OracleKind} {CS} Delta P c Q,
  @semax CS Ora Delta P c Q <-> @semax CS Ora Delta P (remove_skip c) Q.
Proof.
  intros.
  revert P Q.
  induction c; intros; try tauto.
  + simpl.
    assert (semax Delta P (Clight.Ssequence c1 c2) Q <->
            semax Delta P (Clight.Ssequence (remove_skip c1) (remove_skip c2)) Q).
    {
      split; intros HH; apply semax_seq_inv in HH; destruct HH as [R [? ?] ].
      + rewrite IHc1 in H; rewrite IHc2 in H0.
        eapply semax_seq; eauto.
      + rewrite <- IHc1 in H; rewrite <- IHc2 in H0.
        eapply semax_seq; eauto.
    }
    destruct (remove_skip c1), (remove_skip c2);
      solve
        [ auto
        | rewrite H; symmetry; apply semax_skip_seq
        | rewrite H; symmetry; apply semax_seq_skip].
  + simpl.
    split; intros HH; apply semax_ifthenelse_inv in HH.
    - eapply semax_pre'; eauto.
      rewrite andp_comm.
      rewrite exp_andp1.
      apply semax_extract_exists; intros P'.
      rewrite andp_assoc.
      apply semax_extract_prop; intros [? ?].
      rewrite andp_comm.
      apply semax_ifthenelse.
      * apply IHc1, H.
      * apply IHc2, H0.
    - eapply semax_pre'; eauto.
      rewrite andp_comm.
      rewrite exp_andp1.
      apply semax_extract_exists; intros P'.
      rewrite andp_assoc.
      apply semax_extract_prop; intros [? ?].
      rewrite andp_comm.
      apply semax_ifthenelse.
      * apply IHc1, H.
      * apply IHc2, H0.
  + simpl.
    split; intros HH; apply semax_loop_inv in HH.
    - eapply semax_pre'; eauto.
      apply semax_extract_exists; intros Q1.
      apply semax_extract_exists; intros Q2.
      apply semax_extract_prop; intros [? ?].
      eapply semax_loop.
      * apply IHc1, H.
      * apply IHc2, H0.
    - eapply semax_pre'; eauto.
      apply semax_extract_exists; intros Q1.
      apply semax_extract_exists; intros Q2.
      apply semax_extract_prop; intros [? ?].
      eapply semax_loop.
      * apply IHc1, H.
      * apply IHc2, H0.
Qed.

Lemma soundness: forall {Espec CS} Delta
(P:assert) (Q:ret_assert) (s_stm: S_statement)
(c_stm: C_statement s_stm) (c: statement),
remove_skip c = remove_skip (S_statement_to_Clight s_stm) ->
split_Semax Delta P Q (C_split s_stm c_stm) ->
@semax CS Espec Delta P c Q.
Proof.
  intros.
  apply semax_remove_skip.
  rewrite H.
  rewrite <- semax_remove_skip.
  eapply soundness; eauto.
Qed.

Theorem f_reverse_functionally_correct:
  semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
  forward.start_function.
  apply semax_derives.
  Print AClight.S_statement.
  Locate S_statement.
  Locate S_statement_to_Clight.
  Print S_statement_to_Clight.
  Locate C_split.
  eapply (soundness _ _ _ _ f_reverse_hint); [reflexivity | ..].
  match goal with
  | |- context [C_split ?s ?c] =>
    change (C_split s c) with f_reverse_hint_split
  end.
  simpl.
Abort.
