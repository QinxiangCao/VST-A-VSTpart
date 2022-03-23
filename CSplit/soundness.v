Require Import CSplit.AClight.

Require Import VST.floyd.proofauto.
Require Import CSplit.strong.
Require Import CSplit.semantics.

Fixpoint S_statement_to_Clight (s: S_statement) : Clight.statement :=
  match s with
  | Ssequence s1 s2 =>
      Clight.Ssequence 
        (S_statement_to_Clight s1) 
        (S_statement_to_Clight s2)
  | Sassert       => Clight.Sskip
  | Sskip         => Clight.Sskip
  | Sassign e1 e2 => Clight.Sassign e1 e2
  | Scall id e args
      => Clight.Scall id e args
  | Sset id e
      => Clight.Sset id e
  | Sifthenelse e s1 s2
      => Clight.Sifthenelse e 
          (S_statement_to_Clight s1) 
          (S_statement_to_Clight s2)
  | Sloop s1 s2
      => Clight.Sloop 
          (S_statement_to_Clight s1) 
          (S_statement_to_Clight s2)
  | Sbreak => Clight.Sbreak 
  | Scontinue => Clight.Scontinue
  | Sreturn e => Clight.Sreturn e
  end.

Section Soundness.

Context {CS: compspecs} {Espec: OracleKind} (Delta: tycontext).

Require Import Coq.Program.Equality.

Lemma lb_nil_inv: forall {R:Type} {binder:R->Type}
 (cl: @list_binded_of R binder []),
 cl= {}.
Proof with auto.
  intros.
  dependent destruction cl...
Qed.

Lemma lb_cons_inv: forall {R:Type} {binder:R->Type}
 {s: R} {sl: list R}
 (cl: @list_binded_of R binder (s::sl)),
 exists c cl',
 cl= list_binded_cons s c sl cl'.
Proof with auto.
  intros.
  dependent destruction cl...
  exists r', cl...
Qed.

(* Lemma flatten_binds_inv: (R A : Type) (binder : R -> Type) (HA : inhabited A)
(binder_intro : forall r : R, (A -> binder r) -> binder r)
  (s_x:R) (s_res : list R) (c_res' : A -> binder (s_x :: s_res))
(flatten_partial_pres_binds HA (a0 :: s_pres) c_pres') = *)



Lemma given_pre_sound: forall B HA P s_pres 
  (c_pres: B -> C_partial_pres s_pres),
CForall (@pre_to_semax CS Espec Delta P)
  (flatten_partial_pres_binds HA s_pres c_pres) ->
forall b, CForall (@pre_to_semax CS Espec Delta P) (c_pres b).
Proof.
  intros. revert c_pres H b. induction s_pres;intros.
  - intros. rewrite lb_nil_inv . constructor.
  - inversion H.
    apply inj_pair2 in H2. apply inj_pair2 in H4. subst.
    specialize (IHs_pres _ H5).
    destruct (lb_cons_inv (c_pres b)) as [r [cl E]].
    specialize (IHs_pres b).
    unfold tl_of in IHs_pres. rewrite E in IHs_pres.
    rewrite E. constructor;auto.
    simpl in H3. specialize (H3 b).
    unfold hd_of in H3. rewrite E in H3. auto.
Qed.

Lemma given_sound: forall A HA P Q s_res 
  (c_res': A -> C_result s_res),
split_Semax Delta P Q (C_split_given s_res A HA c_res') ->
forall a, split_Semax Delta P Q (c_res' a).
Proof.
  intros. hnf in H.
  destruct s_res.
  - destruct s. simpl in H.
    destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
    hnf. destruct (c_res' a) eqn:E.
    repeat split;auto.
    + clear S2 S3 S4 S5 S6 S7 S8 S9 S10.
      unfold C_result_proj_C_pre in S1.
      unfold flatten_partial_pres_binds in S1.
      apply given_pre_sound with (b:=a) in S1.
      rewrite E in S1. auto.
Admitted.



Lemma given_sound: forall A (HA: inhabited A) P Q s_stm 
  (c_stm' : A -> C_statement s_stm),
split_Semax Delta P Q (C_split s_stm (Cgiven A HA s_stm c_stm')) ->
forall a, split_Semax Delta P Q (C_split s_stm (c_stm' a)).
Proof.
  intros.
  simpl in H.
  set (x:= (fun a : A => C_split s_stm (c_stm' a))) in H.
  change ((C_split s_stm (c_stm' a))) with (x a).
  set (y:= S_split s_stm) in x, H.
  clearbody x.  clearbody y.
  destruct y.
  dependent destruction y.


  remember (C_split s_stm  (Cgiven A HA s_stm c_stm')) as c_res_given.
  dependent destruction c_res_given.
  - rewrite <- x in H.
    rewrite <- x in H.
  destruct (C_split s_stm  (Cgiven A HA s_stm c_stm')).
  - destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
    hnf. destruct (C_split s_stm (c_stm' a)).
    2:{  }
  unfold C_split in H. unfold C_split_given in H.
  simpl in H.


Theorem soundness: forall 
(P:assert) (Q:ret_assert) (s_stm: S_statement)
(c_stm: C_statement s_stm),
split_Semax Delta P Q (C_split s_stm c_stm) ->
@semax CS Espec Delta P (S_statement_to_Clight s_stm) Q.
Proof.
  intros. revert P Q H.


  (* 
  induction s_stm.
  - dependent destruction c_stm.
    { intros. admit. }
    { intros.
      simpl.
      assert (stm1': A -> C_statement s_stm1) by admit.
      assert (stm2': A -> C_statement s_stm2) by admit.
      specialize (IHs_stm1 (Cgiven A HA s_stm1 stm1')).
      admit.
    }
    { admit. }
  - dependent destruction c_stm.
  *)

  induction c_stm.
  - (* Ssequence *)
    intros. simpl.

    simpl in H.
    (* destruct (C_split s1 c_stm1).
    
    destruct (C_split s1 c_stm1) eqn:E.
    2:{ } *)

    admit.
  - (* Sassert *)
    intros. simpl.
    simpl in H.
    destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
    dependent destruction S1.
    dependent destruction S3.
    simpl in H. simpl in H0.
    apply semax_skip_inv in H.
    apply semax_skip_inv in H0.
    admit.

  - (* Sskip *)
    admit.

  - (* given *)
    intros. simpl in H0.
    destruct H0 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).

    admit.

  - (* exgiven *)
    admit.

  - (* assign *)
    admit.

  - (* call *)
    admit.

  - (* set *)
    admit.

  - (* ifthenelse *)
    admit.

  - (* loop *)
    intros. simpl.
    simpl in H.
    destruct (C_split s1 c_stm1).

    admit.




End Soundness.