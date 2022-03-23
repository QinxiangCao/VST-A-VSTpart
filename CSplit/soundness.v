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

Lemma given_sound: forall A (HA: inhabited A) P Q s_stm 
  (c_stm' : A -> C_statement s_stm),
split_Semax Delta P Q (C_split s_stm (Cgiven A HA s_stm c_stm')) ->
forall a, split_Semax Delta P Q (C_split s_stm (c_stm' a)).
Proof.
  intros. 
  hnf in H.

  simpl in H.
  
  set (x:= (fun a : A => C_split s_stm (c_stm' a))) in H.
  change ((C_split s_stm (c_stm' a))) with (x a).
  set (y:= S_split s_stm) in x, H.
  clearbody x. clearbody  y.


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