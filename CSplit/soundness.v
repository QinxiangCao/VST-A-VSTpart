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

Lemma CForall_Capp {A:Type} {binder: A -> Type}:
forall (P : forall (a: A), binder a -> Prop ) 
  {sl1: list A}   (cl1: @list_binded_of A binder sl1)
  {sl2: list A}   (cl2: @list_binded_of A binder sl2),
  CForall P (cl1 +++ cl2) <-> CForall P cl1 /\ CForall P cl2.
Proof.
  intros.
  induction cl1.
  - split;intro.
    + split;try constructor. simpl in H. auto.
    + simpl. destruct H. auto.
  - split;intro.
    + dependent destruction H.
      apply IHcl1 in H0. destruct H0.
       simpl in H. repeat split;try constructor; auto.
    + simpl. destruct H.
      dependent destruction H.
      constructor;auto. apply IHcl1.
      split;auto.
Qed.


Ltac destruct_CForalls S :=
    match type of S with
    | (CForall ?P _)  =>
    repeat (
      match goal with
      | [H : CForall P (_ +++ _) |- _] => 
          let n1 := fresh S "_" in
          let n2 := fresh S "_" in
          apply CForall_Capp in H; destruct H as [n1 n2]
      end
    )
    end.


Lemma rewrite_flatten_binds: forall 
  {R A: Type} {binder: R -> Type}
  (binder_intro : forall (r : R),
      (A -> binder r) -> binder r)
  HA x xs (cs: A -> list_binded_of (x::xs)), 
(flatten_binds HA binder_intro (x :: xs) cs)
= list_binded_cons x (binder_intro x (hd_of x xs cs))
   xs (flatten_binds HA binder_intro xs (tl_of x xs cs)).
Proof.
  intros.
  reflexivity.
Qed.


Lemma path_to_semax_nil_pre: forall Delta A (ass': A ->assert)
  s_pre (c_pre: C_partial_pre s_pre) a,
  path_to_semax Delta (Cpost_conn_Cpre_aux (ass' a) [] c_pre) ->
  pre_to_semax Delta (ass' a) c_pre.
Proof.
  intros.
  induction c_pre.
  - simpl in H. auto.
  - simpl in *. intros a0.
    apply H0 with (a0:=a0).
    auto.
Qed.

Lemma Cpost_conn_Cpres_inv_exgiven: forall A (HA: inhabited A)
  (ass' : A -> assert) (s_pres: S_partial_pres)
  (c_pres': A -> C_partial_pres s_pres),
CForall (@path_to_semax CS Espec Delta)
         (add_exP_to_Cpre HA ass' c_pres') ->
  forall a, CForall (@pre_to_semax CS Espec Delta (ass' a)) (c_pres' a).
Proof.
  intros A HA ass' s_pres.
  induction s_pres;intros.
  - rewrite lb_nil_inv. constructor.
  - inversion H.
    apply inj_pair2 in H2. apply inj_pair2 in H4. subst.
    destruct (lb_cons_inv (c_pres' a0)) as [r [cl E]].
    specialize (IHs_pres _ H5 a0).
    unfold tl_of in IHs_pres. rewrite E in IHs_pres.
    rewrite E. constructor;auto.
    simpl in H3. specialize (H3 a0).
    unfold hd_of in H3. rewrite E in H3. auto.
    apply path_to_semax_nil_pre. auto.
Qed.

Lemma Cpost_conn_atoms_inv_exgiven: forall A (HA: inhabited A) Q
  (ass' : A -> assert) (atoms: atoms),
  CForall (@post_to_semax CS Espec Delta Q)
  (Cposts_conn_atoms
     {bind_C_partial_post A HA (mk_S_partial_post [])
        (fun a : A => mk_C_partial_post (ass' a) [])} atoms) ->
  forall a, Forall (atom_to_semax Delta (ass' a) Q) atoms.
Proof.
  intros.
  induction atoms.
  - constructor.
  - inversion H. apply inj_pair2 in H2.
    apply inj_pair2 in H4. subst.
    constructor.
    { destruct a0. simpl in H3.
      apply H3. }
    { auto. }
Qed.



Lemma Cpost_conn_atom_rets_inv_exgiven: forall A (HA: inhabited A) Q
  (ass' : A -> assert) (atoms: atom_rets),
  CForall (@post_ret_to_semax CS Espec Delta Q)
  (Cposts_conn_returns
     {bind_C_partial_post A HA (mk_S_partial_post [])
        (fun a : A => mk_C_partial_post (ass' a) [])} atoms) ->
  forall a, Forall (atom_ret_to_semax Delta (ass' a) Q) atoms.
Proof.
  intros.
  induction atoms.
  - constructor.
  - inversion H. apply inj_pair2 in H2.
    apply inj_pair2 in H4. subst.
    constructor.
    { destruct a0. simpl in H3.
      apply H3. }
    { auto. }
Qed.


Ltac destruct_Sresult_rec S :=
  let n1 := fresh "s_pre" in
  let n2 := fresh "s_path" in
  let n3 := fresh "s_post_normal" in
  let n4 := fresh "s_post_break" in
  let n5 := fresh "s_post_continue" in
  let n6 := fresh "s_post_return" in
  let n7 := fresh "s_atom_normal" in
  let n8 := fresh "s_atom_break" in
  let n9 := fresh "s_atom_continue" in
  let n10 := fresh "s_atom_return" in
  let n := fresh "Es_res" in
  let t := fresh "S" in
  destruct S as [t|];[destruct t as [n1 n2 n3 n4 n5 n6 n7 n8 n9 n10] eqn:n|].

Lemma ex_given_sound: forall A HA P Q s_res 
  (ass': A -> assert)
  (c_res': A -> C_result s_res),
split_Semax Delta P Q (C_split_exgiven s_res A HA ass' c_res') ->
ENTAIL Delta, allp_fun_id Delta && P |-- exp ass' /\
forall a, split_Semax Delta (ass' a) Q (c_res' a).
Proof.
  intros. hnf in H.
  destruct_Sresult_rec s_res.
  - simpl in H.
    destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
    split.
    (* P |- EX x, ass' x *)
    { dependent destruction S1.
      simpl in H. apply semax_skip_inv in H. auto. }
    (* Split_Semax *)
    intros a. simpl.
    destruct (c_res' a) as [c_pre c_path c_post_normal c_post_break
    c_post_continue c_psot_return] eqn:E.
    repeat split;auto.
    + (* C_pre *)
      destruct_CForalls S2.
      apply Cpost_conn_Cpres_inv_exgiven with (a:=a) in S2_0. unfold C_result_proj_C_pre in S2_0.
      rewrite E in S2_0.
      apply S2_0.
    + (* C_path *)
      destruct_CForalls S2.
      apply given_path_sound with (b:=a) in S2_.
      unfold C_result_proj_C_path in S2_.
      rewrite E in S2_. auto.
    + (* C_post_normal *)
      destruct_CForalls S3.
      apply given_post_sound with (b:=a) in S3_.
      unfold C_result_proj_C_post_normal in S3_.
      rewrite E in S3_. auto.
    + (* C_post_break *)
      destruct_CForalls S4.
      apply given_post_sound with (b:=a) in S4_.
      unfold C_result_proj_C_post_break in S4_.
      rewrite E in S4_. auto.
    + (* C_post_continue *)
      destruct_CForalls S5.
      apply given_post_sound with (b:=a) in S5_.
      unfold C_result_proj_C_post_continue in S5_.
      rewrite E in S5_. auto.
    + (* C_post_return *)
      destruct_CForalls S6.
      apply given_post_ret_sound with (b:=a) in S6_.
      unfold C_result_proj_C_post_return in S6_.
      rewrite E in S6_. auto.
    + (* C_atom_normal *)
      destruct_CForalls S3.
      apply Cpost_conn_atoms_inv_exgiven 
        with (a:=a) in S3_0. auto.
    + (* C_atom_break *)
      destruct_CForalls S4.
      apply Cpost_conn_atoms_inv_exgiven 
        with (a:=a) in S4_0. auto.
    + (* C_atom_continue *)
      destruct_CForalls S5.
      apply Cpost_conn_atoms_inv_exgiven 
        with (a:=a) in S5_0. auto.
    + (* C_atom_return *)
      destruct_CForalls S6.
      apply Cpost_conn_atom_rets_inv_exgiven 
        with (a:=a) in S6_0. auto.
  - simpl in H.
    destruct H.
Qed.

Lemma ENTAIL_FF_left: forall Q,
ENTAIL Delta, allp_fun_id Delta && FF |-- Q.
Proof.
  intros.
  eapply derives_trans;[|apply FF_left].
  solve_andp.
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
    destruct HA.
    (* inhabited used here! *)
    apply H with (a:=a).
    apply given_sound with (a:=a) in H0 .
    auto.

  - (* exgiven *)
    intros. simpl in H0.
    pose proof ex_given_sound _ _ _ _ _ _ _ H0.
    destruct H1. simpl.
    apply semax_seq with (Q0:= exp ass).
    { eapply semax_conseq;
        [apply ENTAIL_refl| ..|apply semax_skip];
        destruct Q;unfold_der; 
          intros; try apply ENTAIL_FF_left.
      eapply derives_trans;[|apply H1];solve_andp.
    }
    apply semax_extract_exists.
    intros a. (* unlike given, inhabited not used *)
    apply H with (a:=a). auto.

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