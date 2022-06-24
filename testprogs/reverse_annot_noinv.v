From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import CSplit.semantics.
Require Import utils.AClightNotations.
Require Import FloydSeq.proofauto.
Require VST.floyd.proofauto.
Require Import FloydSeq.proofauto.
Require Import CSplit.strong.
Require Import FloydSeq.client_lemmas.
Require Import CSplit.strongSoundness.
Require Import CSplit.AClightFunc.


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

Definition f_reverse_hint sh (p: val) l :=
        (Csequence
(*          (Cset _w (Econst_int (Int.repr 0) tint)) *)
          (Cset _w  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
          (Csequence
            (Cset _v (Etempvar _p (tptr (Tstruct _list noattr))))
            (Csequence
              (Cloop
                (Csequence
                  (Cassert (
       (EX w v l1 l2,
          PROP  (writable_share sh; l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert))
                  (EXGIVEN w
                    [[((EX v l1 l2,
          PROP  (writable_share sh; l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert)]] 
                    (EXGIVEN v
                      [[((EX l1 l2,
          PROP  (writable_share sh; l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert)]] 
                      (EXGIVEN l1
                        [[((EX l2,
          PROP  (writable_share sh; l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert)]] 
                        (EXGIVEN l2
                          [[((PROP  (writable_share sh; l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert)]] 
                          (Csequence
                            (Cifthenelse (Etempvar _v (tptr (Tstruct _list noattr)))
                              Cskip
                              (Csequence Cbreak Cskip))
                            (Csequence
                              (Cassert (
         (EX t x l2',
	    PROP  (writable_share sh; l = rev l1 ++ l2; l2 = x :: l2'; writable_share sh)
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert))
                              (EXGIVEN t
                                [[((EX x l2',
	    PROP  (writable_share sh; l = rev l1 ++ l2; l2 = x :: l2'; writable_share sh)
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert)]] 
                                (EXGIVEN x
                                  [[((EX l2',
	    PROP  (writable_share sh; l = rev l1 ++ l2; l2 = x :: l2'; writable_share sh)
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert)]] 
                                  (EXGIVEN l2'
                                    [[((PROP  (writable_share sh; l = rev l1 ++ l2; l2 = x :: l2'; writable_share sh)
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
                Cskip)))).

Definition Gprog : funspecs :=
  ltac:(with_library prog [reverse_spec]).

Time Definition f_reverse_hint_split sh p l:=
  ltac:(compute_split (f_reverse_hint sh p l)).

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

Lemma semax_skip_normal_split_post: forall {Ora CS} Delta P Q,
  P |-- Q ->
  @semax Ora CS Delta P Clight.Sskip (normal_split_assert Q).
Proof.
  intros.
  eapply semax_post_simple with (normal_ret_assert P); [apply H | apply TT_right .. | apply TT_right | intro; apply TT_right | ].
  apply semax_skip.
Qed.

Lemma semax_return_return_split_assert: forall {Ora CS} Delta P c Q F,
  @semax Ora CS Delta P c (frame_ret_assert Q F) ->
  @semax Ora CS Delta P c (return_split_assert (RA_return (frame_ret_assert Q F))).
Proof.
  intros.
  eapply semax_post_simple; [ .. | apply H].
  + apply TT_right.
  + apply TT_right.
  + apply TT_right.
  + intros; apply derives_refl.
Qed.

Theorem f_reverse_functionally_correct:
  semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
  start_function.
  change @client_lemmas.abbreviate with @abbreviate in Delta_specs, Delta.
  apply semax_derives.
  eapply (soundness _ _ _ _ (f_reverse_hint sh p l)); [reflexivity | ..]. 
  match goal with
  | |- context [C_split ?c] =>
    change (C_split c) with (f_reverse_hint_split sh p l)
  end.
  apply split_Semax_fun_equiv.
  unfold f_reverse_hint_split;
    cbv [split_Semax_fun S_split S_split_sequence S_split_assert S_split_set S_split_loop_refined S_split_loop S_split_ifthenelse S_split_break S_split_continue S_split_return S_split_skip S_split_assign
        path_to_semax pre_to_semax post_to_semax post_ret_to_semax atom_to_semax atom_ret_to_semax 
        hd_assert_of_post hd_assert_of_post_ret
        path_to_statement to_Clight
        atoms_conn_atoms atom_conn_atoms atoms_conn_returns atom_conn_returns Sconcat Sapp Smap SForall CForall].
  repeat
    match goal with
    | |- _ /\ _ => split
    | |- True => auto
    | |- _ => intros;
              match goal with
              | |- semax _ _ Clight.Sskip _ => apply semax_skip_normal_split_post, derives_refl
              end
    end.
  + Intros.
    forward.
    forward.
    unfold RA_normal, normal_split_assert.
    Exists nullval p (@nil val) l.
    entailer!.
    unfold listrep.
    entailer!.
  + intros w v l1 l2.
    forward_if; [| forward; apply TT_right].
    forward.
    unfold RA_normal, normal_split_assert.
    sep_apply (listrep_isptr sh l2 v).
    Intros a l2b t.
    Exists t a l2b.
    entailer!.
  + Intros w v l1 l2 t a l2b.
    forward.
    forward.
    forward.
    forward.
    unfold RA_normal, normal_split_assert.
    entailer!.
    Exists v t (a :: l1) l2b.
    entailer!.
    - simpl.
      rewrite <- app_assoc.
      reflexivity.
    - unfold listrep at 2; fold listrep.
      Exists w.
      entailer!.
  + Intros w v l1 l2.
    forward_if; [forward; apply TT_right |].
    unfold POSTCONDITION, abbreviate.
    apply semax_return_return_split_assert.
    forward.
    Exists w; entailer!.
    sep_apply (listrep_null sh l2).
    entailer!.
    rewrite app_nil_r, rev_involutive.
    entailer!.
Qed.
