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
  intros. revert c_pres H b. dependent induction s_pres;intros.
  - intros. rewrite lb_nil_inv . constructor.
  - inversion H.
    apply inj_pair2 in H2. apply inj_pair2 in H4. subst.
    destruct (lb_cons_inv (c_pres b)) as [r [cl E]].
    specialize (IHs_pres _ H5 b).
    unfold tl_of in IHs_pres. rewrite E in IHs_pres.
    rewrite E. constructor;auto.
    simpl in H3. specialize (H3 b).
    unfold hd_of in H3. rewrite E in H3. auto.
Qed.


Lemma given_post_sound: forall B HA P s_posts 
  (c_posts: B -> C_partial_posts s_posts),
CForall (@post_to_semax CS Espec Delta P)
  (flatten_partial_posts_binds HA s_posts c_posts) ->
forall b, CForall (@post_to_semax CS Espec Delta P) (c_posts b).
Proof.
  intros. revert c_posts H b. dependent induction s_posts;intros.
  - intros. rewrite lb_nil_inv . constructor.
  - inversion H.
    apply inj_pair2 in H2. apply inj_pair2 in H4. subst.
    destruct (lb_cons_inv (c_posts b)) as [r [cl E]].
    specialize (IHs_posts _ H5 b).
    unfold tl_of in IHs_posts. rewrite E in IHs_posts.
    rewrite E. constructor;auto.
    simpl in H3. specialize (H3 b).
    unfold hd_of in H3. rewrite E in H3. auto.
Qed.


Lemma given_post_ret_sound: forall B HA P s_posts 
  (c_posts: B -> C_partial_post_rets s_posts),
CForall (@post_ret_to_semax CS Espec Delta P)
  (flatten_partial_post_rets_binds HA s_posts c_posts) ->
forall b, CForall (@post_ret_to_semax CS Espec Delta P) (c_posts b).
Proof.
  intros. revert c_posts H b. dependent induction s_posts;intros.
  - intros. rewrite lb_nil_inv . constructor.
  - inversion H.
    apply inj_pair2 in H2. apply inj_pair2 in H4. subst.
    destruct (lb_cons_inv (c_posts b)) as [r [cl E]].
    specialize (IHs_posts _ H5 b).
    unfold tl_of in IHs_posts. rewrite E in IHs_posts.
    rewrite E. constructor;auto.
    simpl in H3. specialize (H3 b).
    unfold hd_of in H3. rewrite E in H3. auto.
Qed.

Lemma given_path_sound: forall B HA  s_paths 
  (c_paths: B -> C_full_paths s_paths),
CForall (@path_to_semax CS Espec Delta)
  (flatten_full_paths_binds HA s_paths c_paths) ->
forall b, CForall (@path_to_semax CS Espec Delta ) (c_paths b).
Proof.
  intros. revert c_paths H b. dependent induction s_paths;intros.
  - intros. rewrite lb_nil_inv . constructor.
  - inversion H.
    apply inj_pair2 in H2. apply inj_pair2 in H4. subst.
    destruct (lb_cons_inv (c_paths b)) as [r [cl E]].
    specialize (IHs_paths _ H5 b).
    unfold tl_of in IHs_paths. rewrite E in IHs_paths.
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
    + apply given_pre_sound with (b:=a) in S1.
      unfold C_result_proj_C_pre in S1.
      rewrite E in S1. auto.
    + apply given_path_sound with (b:=a) in S2.
      unfold C_result_proj_C_path in S2.
      rewrite E in S2. auto.
    + apply given_post_sound with (b:=a) in S3.
      unfold C_result_proj_C_post_normal in S3.
      rewrite E in S3. auto.
    + apply given_post_sound with (b:=a) in S4.
      unfold C_result_proj_C_post_break in S4.
      rewrite E in S4. auto.
    + apply given_post_sound with (b:=a) in S5.
      unfold C_result_proj_C_post_continue in S5.
      rewrite E in S5. auto.
    + apply given_post_ret_sound with (b:=a) in S6.
      unfold C_result_proj_C_post_return in S6.
      rewrite E in S6. auto.
  - destruct H.
Qed.


Theorem soundness: forall 
(P:assert) (Q:ret_assert) (s_stm: S_statement)
(c_stm: C_statement s_stm),
split_Semax Delta P Q (C_split s_stm c_stm) ->
@semax CS Espec Delta P (S_statement_to_Clight s_stm) Q.
Proof.
  intros. revert P Q H.
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
    destruct HA. apply H with (a:=a).
    apply given_sound with (a:=a) in H0 .
    auto.

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