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


(****************************)
(****************************)
(* Given Soundness *)
(****************************)
(****************************)


Lemma given_pre_sound: forall B HA P s_pres 
  (c_pres: B -> C_partial_pres s_pres),
CForall (@pre_to_semax CS Espec Delta P)
  (flatten_partial_pres_binds HA s_pres c_pres) ->
forall b, CForall (@pre_to_semax CS Espec Delta P) (c_pres b).
Proof.
  intros. revert c_pres H b. dependent induction s_pres;intros.
  - intros. rewrite lb_nil_inv . constructor.
  - destruct a. destruct H.
    destruct (C_partial_pres_inv (c_pres b)) as [r [cl E]].
    specialize (IHs_pres _ H0 b).
    unfold tl_of in IHs_pres. rewrite E in IHs_pres.
    rewrite E. constructor;auto.
    simpl.
    eapply semax_post'';[|apply H].
    apply andp_left2. simpl. intro w.
    eapply derives_trans.
    { apply allp_instantiate' with (x:=b). }
    rewrite E. apply derives_refl.
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
    destruct (lb_cons_inv (c_posts b)) as [r [cl E]].
    specialize (IHs_posts _ H1 b).
    unfold tl_of in IHs_posts. rewrite E in IHs_posts.
    rewrite E. constructor;auto.
    simpl in H0. specialize (H0 b).
    unfold hd_of in H0. rewrite E in H0. auto.
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
    destruct (lb_cons_inv (c_posts b)) as [r [cl E]].
    specialize (IHs_posts _ H1 b).
    unfold tl_of in IHs_posts. rewrite E in IHs_posts.
    rewrite E. constructor;auto.
    simpl in H0. specialize (H0 b).
    unfold hd_of in H0. rewrite E in H0. auto.
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
    destruct (lb_cons_inv (c_paths b)) as [r [cl E]].
    specialize (IHs_paths _ H1 b).
    unfold tl_of in IHs_paths. rewrite E in IHs_paths.
    rewrite E. constructor;auto.
    simpl in H0. specialize (H0 b).
    unfold hd_of in H0. rewrite E in H0. auto.
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


(****************************)
(****************************)
(* EX-Given  Soundness *)
(****************************)
(****************************)


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
  (* - simpl in *. intros a0.
    apply H0 with (a0:=a0).
    auto. *)
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
    destruct (lb_cons_inv (c_pres' a0)) as [r [cl E]].
    specialize (IHs_pres _ H1 a0).
    unfold tl_of in IHs_pres. rewrite E in IHs_pres.
    rewrite E. constructor;auto.
    simpl in H0. specialize (H0 a0).
    unfold hd_of in H0. rewrite E in H0. auto.
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
  - destruct H. 
    constructor.
    { destruct a0. simpl in H.
      apply H. }
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
  - inversion H.
    constructor.
    { destruct a0. simpl in H.
      apply H. }
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

(****************************)
(****************************)
(* Basic Constructor Soundness *)
(****************************)
(****************************)

Lemma ENTAIL_FF_left: forall Q,
ENTAIL Delta, allp_fun_id Delta && FF |-- Q.
Proof.
  intros.
  eapply derives_trans;[|apply FF_left].
  solve_andp.
Qed.

Lemma semax_skip_der: forall Q,
semax Delta (RA_normal Q) Clight.Sskip Q.
Proof.
  intros.
  destruct Q;unfold_der.
  eapply semax_post'';[..|apply semax_skip];unfold_der;
    try solve [intros; apply ENTAIL_FF_left].
  solve_andp.
Qed.

Lemma assert_sound: forall P Q a,
  split_Semax Delta P Q (C_split Sassert (Cassert a)) ->
  semax Delta P Clight.Sskip Q.
Proof.
  intros.
  simpl.
  simpl in H.
  destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  dependent destruction S1.
  dependent destruction S3.
  simpl in H. simpl in H0.
  apply semax_skip_inv in H.
  apply semax_skip_inv in H1.
  eapply semax_pre';[apply H|..].
  eapply semax_pre';[apply H1|..].
  rewrite normal_ret_assert_elim.
  apply semax_skip_der.
Qed.



(****************************)
(****************************)
(* Compound Constructor Soundness *)
(****************************)
(****************************)


(*-------------------------
Tactics for combining proofs 
for individual path/partial_paths
-------------------------*)
Ltac merge_Q2:=
  let Q1 := fresh "Q" in
  let Q2 := fresh "Q" in
  Intros Q1; Intros Q2; Exists (andp Q1 Q2);
  repeat apply andp_right; try solve_andp.

Ltac merge_Q1:=
  let Q := fresh "Q" in
  Intros Q; Exists Q;
  repeat apply andp_right; try solve_andp.

Ltac merge_Q3:=
  let Q1 := fresh "Q" in
  let Q2 := fresh "Q" in
  let Q3 := fresh "Q" in
  Intros Q1; Intros Q2; Intros Q3; 
  Exists (Q1 && (Q2 && Q3));
  repeat apply andp_right; try solve_andp.

Ltac merge_Q4:=
  let Q1 := fresh "Q" in
  let Q2 := fresh "Q" in
  let Q3 := fresh "Q" in
  let Q4 := fresh "Q" in
  Intros Q1; Intros Q2; Intros Q3;  Intros Q4;
  Exists (Q1 && (Q2 && (Q3 && Q4)));
  repeat apply andp_right; try solve_andp.

Ltac merge_Q5:=
  let Q1 := fresh "Q" in
  let Q2 := fresh "Q" in
  let Q3 := fresh "Q" in
  let Q4 := fresh "Q" in
  let Q5 := fresh "Q" in
  Intros Q1; Intros Q2; Intros Q3;  Intros Q4; Intros Q5;
  Exists (Q1 && (Q2 && (Q3 && (Q4 && Q5))));
  repeat apply andp_right; try solve_andp.

Ltac merge_Q6:=
  let Q1 := fresh "Q" in
  let Q2 := fresh "Q" in
  let Q3 := fresh "Q" in
  let Q4 := fresh "Q" in
  let Q5 := fresh "Q" in
  let Q6 := fresh "Q" in
  Intros Q1; Intros Q2; Intros Q3;  Intros Q4; Intros Q5; Intros Q6;
  Exists (Q1 && (Q2 && (Q3 && (Q4 && (Q5 && Q6)))));
  repeat apply andp_right; try solve_andp.

Ltac solve_split:=
  match goal with
  | E: Forall (atom_ret_to_semax Delta _ ?R) ?ret_atoms 
    |- Forall (atom_ret_to_semax Delta ?Q ?R) ?ret_atoms => 
      eapply atom_return_to_semax_derives_pre_group;[|apply E]; solve_andp
  | E: Forall (atom_to_semax Delta _ ?R) ?ret_atoms 
      |- Forall (atom_to_semax Delta ?Q ?R) ?ret_atoms => 
        eapply atom_to_semax_derives_pre_group;[|apply E]; solve_andp
  | E: CForall (@pre_to_semax _ _ Delta _) ?pres 
    |- CForall (@pre_to_semax _ _ Delta _) ?pres => 
      eapply pre_to_semax_derives_group;[|apply E]; solve_andp
  end.

Lemma remove_entail: forall P Q,
  P |-- Q ->
  ENTAIL Delta, P |-- Q.
Proof.
  intros. apply andp_left2. auto.
Qed.


Ltac combine_aux_post_auto:=
  match goal with
  | t: C_partial_pres [] |- _ => 
    rewrite (lb_nil_inv t) in *
  | _ => idtac
  end;
  match goal with
  | E1: CForall (@post_to_semax _ _ Delta _) ?T,
    E2: CForall (@post_to_semax _ _ Delta _) ?T,
    E3: CForall (@post_to_semax _ _ Delta _) ?T,
    E4: CForall (@post_to_semax _ _ Delta _) ?T,
    E5: CForall (@post_to_semax _ _ Delta _) ?T,
    E6: CForall (@post_to_semax _ _ Delta _) ?T|-
    CForall (@post_to_semax _ _ Delta _) ?T =>
    eapply post_to_semax_derives_group;
    [|eapply post_to_semax_conj_rule_group;
      [apply E1|
        eapply post_to_semax_conj_rule_group;
        [apply E2|
        eapply post_to_semax_conj_rule_group;
        [apply E3|
          eapply post_to_semax_conj_rule_group;
          [apply E4|
          eapply post_to_semax_conj_rule_group;
            [apply E5|apply E6]]]]]];
    try (apply remove_entail);
    merge_Q6; apply prop_right;
    repeat split;try solve [constructor]; try solve_split
    | E1: CForall (@post_to_semax _ _ Delta _) ?T,
      E2: CForall (@post_to_semax _ _ Delta _) ?T,
      E3: CForall (@post_to_semax _ _ Delta _) ?T,
      E4: CForall (@post_to_semax _ _ Delta _) ?T,
      E5: CForall (@post_to_semax _ _ Delta _) ?T|-
      CForall (@post_to_semax _ _ Delta _) ?T =>
      eapply post_to_semax_derives_group;
      [|eapply post_to_semax_conj_rule_group;
         [apply E1|
          eapply post_to_semax_conj_rule_group;
          [apply E2|
           eapply post_to_semax_conj_rule_group;
           [apply E3|
            eapply post_to_semax_conj_rule_group;
            [apply E4|apply E5]]]]];
      try (apply remove_entail);
      merge_Q5; apply prop_right;
      repeat split;try solve [constructor]; try solve_split
    | E1: CForall (@post_to_semax _ _ Delta _) ?T,
      E2: CForall (@post_to_semax _ _ Delta _) ?T,
      E3: CForall (@post_to_semax _ _ Delta _) ?T,
      E4: CForall (@post_to_semax _ _ Delta _) ?T |-
      CForall (@post_to_semax _ _ Delta _) ?T =>
      eapply post_to_semax_derives_group;
      [|eapply post_to_semax_conj_rule_group;
         [apply E1|
          eapply post_to_semax_conj_rule_group;
          [apply E2|
           eapply post_to_semax_conj_rule_group;
           [apply E3|apply E4]]]];
           try (apply remove_entail);
           merge_Q4; apply prop_right;
           repeat split;try solve [constructor]; try solve_split
    | E1: CForall (@post_to_semax _ _ Delta _) ?T,
      E2: CForall (@post_to_semax _ _ Delta _) ?T,
      E3: CForall (@post_to_semax _ _ Delta _) ?T |-
      CForall (@post_to_semax _ _ Delta _) ?T =>
      eapply post_to_semax_derives_group;
      [|eapply post_to_semax_conj_rule_group;
         [apply E1|
         eapply post_to_semax_conj_rule_group;[apply E2|apply E3]]];
         try (apply remove_entail);
         merge_Q3; apply prop_right;
         repeat split;try solve [constructor]; try solve_split
    | E1: CForall (@post_to_semax _ _ Delta _) ?T,
      E2: CForall (@post_to_semax _ _ Delta _) ?T|-
      CForall (@post_to_semax _ _ Delta _) ?T =>
      eapply post_to_semax_derives_group;
        [|eapply post_to_semax_conj_rule_group;[apply E1|apply E2]];
        try (apply remove_entail);
      merge_Q2; apply prop_right;
      repeat split;try solve [constructor]; try solve_split
    | E1: CForall (@post_to_semax _ _ Delta _) ?T |-
      CForall (@post_to_semax _ _ Delta _) ?T =>
      let Q1 := fresh "Q" in
      eapply post_to_semax_derives_group;
      [|apply E1];try (apply remove_entail);
      merge_Q1; apply prop_right; repeat split;
      try solve [constructor]; try solve_split
    | _ => idtac
   end.

Ltac combine_aux_atom_auto:=
match goal with
| t: C_partial_pres [] |- _ => 
  rewrite (lb_nil_inv t) in *
| _ => idtac
end;
match goal with
  | E1: Forall (atom_to_semax Delta _ _) ?T,
    E2: Forall (atom_to_semax Delta _ _) ?T,
    E3: Forall (atom_to_semax Delta _ _) ?T,
    E4: Forall (atom_to_semax Delta _ _) ?T,
    E5: Forall (atom_to_semax Delta _ _) ?T|-
    Forall (atom_to_semax Delta _ _) ?T =>
    eapply atom_to_semax_derives_post_group;
    [|eapply atom_to_semax_conj_rule_group;
        [apply E1|
        eapply atom_to_semax_conj_rule_group;
        [apply E2|
          eapply atom_to_semax_conj_rule_group;
          [apply E3|
          eapply atom_to_semax_conj_rule_group;
          [apply E4|apply E5]]]]];
    try (apply remove_entail);
    merge_Q5; apply prop_right;
    repeat split;try solve [constructor]; try solve_split
  | E1: Forall (atom_to_semax Delta _ _) ?T,
    E2: Forall (atom_to_semax Delta _ _) ?T,
    E3: Forall (atom_to_semax Delta _ _) ?T,
    E4: Forall (atom_to_semax Delta _ _) ?T |-
    Forall (atom_to_semax Delta _ _) ?T =>
    eapply atom_to_semax_derives_post_group;
    [|eapply atom_to_semax_conj_rule_group;
        [apply E1|
        eapply atom_to_semax_conj_rule_group;
        [apply E2|
          eapply atom_to_semax_conj_rule_group;
          [apply E3|apply E4]]]];
          try (apply remove_entail);
          merge_Q4; apply prop_right;
          repeat split;try solve [constructor]; try solve_split
  | E1: Forall (atom_to_semax Delta _ _) ?T,
    E2: Forall (atom_to_semax Delta _ _) ?T,
    E3: Forall (atom_to_semax Delta _ _) ?T |-
    Forall (atom_to_semax Delta _ _) ?T =>
    eapply atom_to_semax_derives_post_group;
    [|eapply atom_to_semax_conj_rule_group;
        [apply E1|
        eapply atom_to_semax_conj_rule_group;[apply E2|apply E3]]];
        try (apply remove_entail);
        merge_Q3; apply prop_right;
        repeat split;try solve [constructor]; try solve_split
  | E1: Forall (atom_to_semax Delta _ _) ?T,
    E2: Forall (atom_to_semax Delta _ _) ?T|-
    Forall (atom_to_semax Delta _ _) ?T =>
    eapply atom_to_semax_derives_post_group;
      [|eapply atom_to_semax_conj_rule_group;[apply E1|apply E2]];
      try (apply remove_entail);
    merge_Q2; apply prop_right;
    repeat split;try solve [constructor]; try solve_split
  | E1: Forall (atom_to_semax Delta _ _) ?T |-
    Forall (atom_to_semax Delta _ _) ?T =>
    let Q1 := fresh "Q" in
    eapply atom_to_semax_derives_post_group;
    [|apply E1];try (apply remove_entail);
    merge_Q1; apply prop_right; repeat split;
    try solve [constructor]; try solve_split
  | _ => idtac
  end.


Lemma seq_soundness: forall P Q s_res1 s_res2
  (c_res1: C_result s_res1) (c_res2: C_result s_res2),
  s_res_has_path s_res2 ->
  split_Semax Delta P Q
    (C_split_sequence s_res1 s_res2 c_res1 c_res2) ->
  exists R,
    split_Semax Delta P (overridePost R Q) c_res1 /\
    split_Semax Delta R Q c_res2.
Proof.
  intros P Q s_res1 s_res2. intros c_res1 c_res2.
  intros Hpath H.
  destruct s_res1 as [s_res1|];
  [destruct s_res1 as [
    s_pre1 s_path1 
    s_post_normal1 s_post_break1 s_post_continue1 s_post_return1
    s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1]|].
  2:{ simpl in H. destruct H. }
  destruct s_res2 as [s_res2|];
  [destruct s_res2 as [
    s_pre2 s_path2
    s_post_normal2 s_post_break2 s_post_continue2 s_post_return2
    s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2]|].
  2:{ simpl in H. destruct H. }
  simpl in H.
  destruct c_res1 as [
    c_pre1 c_path1 c_post_normal1 c_post_break1
    c_post_continue1 c_post_return1] eqn:Ec1,
    c_res2 as [
    c_pre2 c_path2 c_post_normal2 c_post_break2
    c_post_continue2 c_post_return2] eqn:Ec2.
  destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  destruct_FForalls.

  apply atoms_conn_pres_group_inv in S19.
  apply posts_conn_pres_group_inv in S18.
  apply posts_conn_atoms_group_inv in S16.
  apply posts_conn_atoms_group_inv in S15.
  apply posts_conn_atoms_group_inv in S13.
  apply posts_conn_returns_group_inv in S11.
  apply atoms_conn_atoms_group_inv in S7.
  apply atoms_conn_atoms_group_inv in S22.
  apply atoms_conn_atoms_group_inv in S21.
  apply atoms_conn_returns_group_inv in S20.

  exists (
    EX R, R && !! (
      CForall (@pre_to_semax CS Espec Delta R) c_pre2
    /\ Forall (atom_to_semax Delta R (RA_normal Q)) s_atom_normal2
    /\ Forall (atom_to_semax Delta R (RA_break Q)) s_atom_break2
    /\ Forall (atom_to_semax Delta R (RA_continue Q)) s_atom_continue2
    /\ Forall (atom_ret_to_semax Delta R (RA_return Q)) s_atom_return2
    )). split.
  
  + repeat split;auto.
    * 
      rewrite overridePost_normal'.
      destruct s_pre2,s_atom_normal2,
      s_atom_break2,s_atom_continue2,s_atom_return2;
      try apply exclude_nil_cons in S18;
      try apply exclude_nil_cons in S16;
      try apply exclude_nil_cons in S13;
      try apply exclude_nil_cons in S11;
      try apply exclude_nil_cons in S15;
      [exfalso; apply Hpath; repeat split;auto|..];
      combine_aux_post_auto.
    * eapply post_to_semax_derives_group;[|apply S4].
      destruct Q;unfold_der. solve_andp.
    * eapply post_to_semax_derives_group;[|apply S5].
      destruct Q;unfold_der. solve_andp.
    * eapply post_ret_to_semax_derives_group;[|apply S6].
      destruct Q;unfold_der. intros. solve_andp.
    * 
      rewrite overridePost_normal'.
      destruct s_pre2,s_atom_normal2,
      s_atom_break2,s_atom_continue2,s_atom_return2;
      try apply exclude_nil_cons in S20;
      try apply exclude_nil_cons in S21;
      try apply exclude_nil_cons in S22;
      try apply exclude_nil_cons in S7;
      try apply exclude_nil_cons in S19;
      [exfalso; apply Hpath; repeat split;auto|..];
      combine_aux_atom_auto.
    * eapply atom_to_semax_derives_post_group;[|apply S8].
      destruct Q;unfold_der. solve_andp.
    * eapply atom_to_semax_derives_post_group;[|apply S9].
      destruct Q;unfold_der. solve_andp.
    * eapply atom_return_to_semax_derives_post_group;[|apply S10].
      destruct Q;unfold_der. intros. solve_andp.
  + repeat split;auto.
    * eapply pre_to_semax_derives_group;[|apply pre_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
    * eapply atom_to_semax_derives_pre_group;
      [|apply atom_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
    * eapply atom_to_semax_derives_pre_group;
      [|apply atom_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
    * eapply atom_to_semax_derives_pre_group;
      [|apply atom_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
    * eapply atom_return_to_semax_derives_pre_group;
      [|apply atom_return_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
Qed.


Lemma loop_soundness: forall P Q s_res1 s_res2
  (c_res1: C_result s_res1) (c_res2: C_result s_res2),
  s_res_has_path s_res2 ->
  split_Semax Delta P Q
    (C_split_loop_refined s_res1 s_res2 c_res1 c_res2) ->
  exists R,
    split_Semax Delta P (loop1_ret_assert R Q) c_res1 /\
    split_Semax Delta R (loop1_ret_assert P Q) c_res2.
Proof.
  intros P Q s_res1 s_res2. intros c_res1 c_res2.
  intros Hpath H.
  destruct s_res1 as [s_res1|];
  [destruct s_res1 as [
    s_pre1 s_path1 
    s_post_normal1 s_post_break1 s_post_continue1 s_post_return1
    s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1]|].
  2:{ simpl in H. destruct H. }
  destruct s_res2 as [s_res2|];
  [destruct s_res2 as [
    s_pre2 s_path2
    s_post_normal2 s_post_break2 s_post_continue2 s_post_return2
    s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2]|].
  2:{ simpl in H. destruct H. }

  destruct s_atom_normal2.
  { destruct c_res1 as [
    c_pre1 c_path1 c_post_normal1 c_post_break1
    c_post_continue1 c_post_return1] eqn:Ec1,
    c_res2 as [
    c_pre2 c_path2 c_post_normal2 c_post_break2
    c_post_continue2 c_post_return2] eqn:Ec2.
    destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
    destruct_FForalls.

  destruct Q as [ Qn Qb Qc Qr];unfold_der.

  apply atoms_conn_pres_group_inv in S35.
  apply atoms_conn_pres_group_inv in S36.
  apply posts_conn_pres_group_inv in S27.
  apply posts_conn_pres_group_inv in S28.
  apply posts_conn_pres_group_inv in S29.
  apply posts_conn_pres_group_inv in S30.
  apply posts_conn_pres_group_inv in S31.
  apply posts_conn_pres_group_inv in S32.
  apply posts_conn_pres_group_inv in S33.
  apply posts_conn_atoms_group_inv in S19.
  apply posts_conn_atoms_group_inv in S20.
  apply posts_conn_atoms_group_inv in S21.
  apply posts_conn_atoms_group_inv in S22.
  apply posts_conn_atoms_group_inv in S23.
  apply posts_conn_atoms_group_inv in S24.
  apply posts_conn_atoms_group_inv in S25.
  apply posts_conn_returns_group_inv in S11.
  apply posts_conn_returns_group_inv in S12.
  apply posts_conn_returns_group_inv in S13.
  apply posts_conn_returns_group_inv in S14.
  apply posts_conn_returns_group_inv in S15.
  apply posts_conn_returns_group_inv in S16.
  apply posts_conn_returns_group_inv in S17.
  apply atoms_conn_atoms_group_inv in S41.
  apply atoms_conn_atoms_group_inv in S42.
  apply atoms_conn_atoms_group_inv in S43.
  apply atoms_conn_returns_group_inv in S38.
  apply atoms_conn_returns_group_inv in S39.
  apply atoms_conn_returns_group_inv in S40.


  exists (
  EX R:assert, andp R (
    !!
      ( CForall (@pre_to_semax CS Espec Delta R) c_pre2 /\
        CForall (@pre_to_semax CS Espec Delta R) 
            (atoms_conn_Cpres [] c_pre1) /\
        Forall (atom_ret_to_semax Delta R Qr) s_atom_return2 /\
        Forall (atom_to_semax Delta R Qn) s_atom_break2 /\
        Forall (atom_to_semax Delta R Qn) 
            (atoms_conn_atoms [] s_atom_break1) /\
        Forall (atom_ret_to_semax Delta R Qr) 
            (atoms_conn_returns [] s_atom_return1)) 
    )).

  
  + repeat split;unfold  loop1_ret_assert;unfold_der;auto.
    * 
      destruct s_pre2,
      s_atom_break2,s_atom_continue2,s_atom_return2;
      try apply exclude_nil_cons in S27;
      try apply exclude_nil_cons in S30;
      try apply exclude_nil_cons in S19;
      try apply exclude_nil_cons in S24;
      try apply exclude_nil_cons in S11;
      try apply exclude_nil_cons in S16;
      [exfalso; apply Hpath; repeat split;auto|..];
      combine_aux_post_auto.
      pose S37.
      destruct a. destruct c. 

      Search c_post_normal1.
      hnf in H.

      Search semax FF.


      unfold add_Q_to_Catoms in c. simpl in c.
      eapply post_to_semax_derives_group with (Q1:=FF);auto.

      hnf in Hpath.
      eapply post_to_semax_derives_group;
      [|eapply post_to_semax_conj_rule_group;
        [apply E1|
          eapply post_to_semax_conj_rule_group;
          [apply E2|
          eapply post_to_semax_conj_rule_group;
          [apply E3|
            eapply post_to_semax_conj_rule_group;
            [apply E4|
            eapply post_to_semax_conj_rule_group;
              [apply E5|apply E6]]]]]];
      try (apply remove_entail);
      merge_Q6; apply prop_right;

    * eapply post_to_semax_derives_group;[|apply S4].
      destruct Q;unfold_der. solve_andp.
    * eapply post_to_semax_derives_group;[|apply S5].
      destruct Q;unfold_der. solve_andp.
    * eapply post_ret_to_semax_derives_group;[|apply S6].
      destruct Q;unfold_der. intros. solve_andp.
    * 
      rewrite overridePost_normal'.
      destruct s_pre2,s_atom_normal2,
      s_atom_break2,s_atom_continue2,s_atom_return2;
      try apply exclude_nil_cons in S20;
      try apply exclude_nil_cons in S21;
      try apply exclude_nil_cons in S22;
      try apply exclude_nil_cons in S7;
      try apply exclude_nil_cons in S19;
      [exfalso; apply Hpath; repeat split;auto|..];
      combine_aux_atom_auto.
    * eapply atom_to_semax_derives_post_group;[|apply S8].
      destruct Q;unfold_der. solve_andp.
    * eapply atom_to_semax_derives_post_group;[|apply S9].
      destruct Q;unfold_der. solve_andp.
    * eapply atom_return_to_semax_derives_post_group;[|apply S10].
      destruct Q;unfold_der. intros. solve_andp.
  + repeat split;auto.
    * eapply pre_to_semax_derives_group;[|apply pre_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
    * eapply atom_to_semax_derives_pre_group;
      [|apply atom_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
    * eapply atom_to_semax_derives_pre_group;
      [|apply atom_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
    * eapply atom_to_semax_derives_pre_group;
      [|apply atom_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
    * eapply atom_return_to_semax_derives_pre_group;
      [|apply atom_return_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
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
    apply seq_soundness in H.
    2:{ apply S_split_has_path. }
    destruct H as [R [H1 H2]].
    eapply semax_seq with (Q0:=R).
    { apply IHc_stm1. auto. }
    { apply IHc_stm2. auto. }

  - (* Sassert *)
    intros. apply assert_sound with (a:=a). auto.

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
    eapply semax_loop.
    admit.

  - (* break *)
    admit.

  - (* continue *)
    admit.

  - (* return *)
    admit.

Admitted.

End Soundness.