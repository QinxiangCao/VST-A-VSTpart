Require Import VST.floyd.proofauto.
Require Import Csplit.semantics_lemmas.
Require Import Csplit.semantics.
Require Import Csplit.strong.
Require Import Coq.Program.Equality.
Require Import Csplit.AClight.
Open Scope aclight_scope.
Local Open Scope logic.

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


(****************************)
(****************************)
(* Given Soundness *)
(****************************)
(****************************)


Lemma given_post_sound: forall B P s_posts 
  (c_posts: B -> C_partial_posts s_posts),
CForall (@post_to_semax CS Espec Delta P)
  (flatten_partial_posts_binds s_posts c_posts) ->
forall b, CForall (@post_to_semax CS Espec Delta P) (c_posts b).
Proof.
  intros. revert c_posts H b. dependent induction s_posts;intros.
  - intros. rewrite lb_nil_inv . constructor.
  - destruct a. 
    inversion H.
    destruct (lb_cons_inv (c_posts b)) as [r [cl E]].
    rewrite E.
    dependent destruction r.
    constructor.
    { eapply semax_pre'.
      2:{ hnf in H0. apply H0. }
      apply exp_right with (x:=b). simpl.
      rewrite E. intros. solve_andp. }
    specialize (IHs_posts _ H1 b).
    unfold tl_of in IHs_posts. rewrite E in IHs_posts.
    auto.
Qed.


Lemma given_post_ret_sound: forall B P s_posts 
  (c_posts: B -> C_partial_post_rets s_posts),
CForall (@post_ret_to_semax CS Espec Delta P)
  (flatten_partial_post_rets_binds s_posts c_posts) ->
forall b, CForall (@post_ret_to_semax CS Espec Delta P) (c_posts b).
Proof.
  intros. revert c_posts H b. dependent induction s_posts;intros.
  - intros. rewrite lb_nil_inv . constructor.
  - destruct a. 
    inversion H.
    destruct (lb_cons_inv (c_posts b)) as [r [cl E]].
    rewrite E.
    dependent destruction r.
    constructor.
    { eapply semax_pre'.
      2:{ hnf in H0. apply H0. }
      apply exp_right with (x:=b). simpl.
      rewrite E. intros. solve_andp. }
    specialize (IHs_posts _ H1 b).
    unfold tl_of in IHs_posts. rewrite E in IHs_posts.
    auto.
Qed.

Lemma given_path_sound: forall B  s_paths 
  (c_paths: B -> C_full_paths s_paths),
CForall (@path_to_semax CS Espec Delta)
  (flatten_full_paths_binds s_paths c_paths) ->
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


(****************************)
(****************************)
(* EX-Given  Soundness *)
(****************************)
(****************************)


Lemma rewrite_flatten_binds: forall 
  {R A: Type} {binder: R -> Type}
  (binder_intro : forall (r : R),
      (A -> binder r) -> binder r)
  x xs (cs: A -> list_binded_of (x::xs)), 
(flatten_binds binder_intro (x :: xs) cs)
= list_binded_cons x (binder_intro x (hd_of x xs cs))
   xs (flatten_binds binder_intro xs (tl_of x xs cs)).
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

Lemma Cpost_conn_Cpres_inv_exgiven: forall A 
  (ass' : A -> assert) (s_pres: S_partial_pres)
  (c_pres': A -> C_partial_pres s_pres),
CForall (@path_to_semax CS Espec Delta)
         (add_exP_to_Cpre ass' c_pres') ->
  forall a, CForall (@pre_to_semax CS Espec Delta (ass' a)) (c_pres' a).
Proof.
  intros A ass' s_pres.
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

Lemma Cpost_conn_atoms_inv_exgiven: forall A Q
  (ass' : A -> assert) (atoms: atoms),
  CForall (@post_to_semax CS Espec Delta Q)
  (Cposts_conn_atoms
     {mk_C_partial_post (fun a : environ => EX x : A, ass' x a) []} atoms) ->
  forall a, Forall (atom_to_semax Delta (ass' a) Q) atoms.
Proof.
  intros.
  induction atoms.
  - constructor.
  - destruct H. 
    constructor.
    { destruct a0. simpl in H.
      simpl. eapply semax_pre'.
      2:{ apply H. } simpl. intros.
      apply exp_right with (x0:=a). solve_andp. }
    { auto. }
Qed.


Lemma Cpost_conn_atom_rets_inv_exgiven: forall A Q
  (ass' : A -> assert) (atoms: atom_rets),
  CForall (@post_ret_to_semax CS Espec Delta Q)
  (Cposts_conn_returns
  {mk_C_partial_post (fun a : environ => EX x : A, ass' x a) []}
   atoms) ->
  forall a, Forall (atom_ret_to_semax Delta (ass' a) Q) atoms.
Proof.
  intros.
  induction atoms.
  - constructor.
  - destruct H. 
    constructor.
    { destruct a0. simpl in H.
      simpl. eapply semax_pre'.
      2:{ apply H. } simpl. intros.
      apply exp_right with (x0:=a). solve_andp. }
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

Lemma ex_given_sound: forall A P Q s_res 
  (ass': A -> assert)
  (c_res': A -> C_result s_res),
split_Semax Delta P Q (C_split_exgiven s_res A ass' c_res') ->
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
  rewrite normal_split_assert_elim.
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

Ltac clean_nil :=
  repeat 
  (try rewrite !atoms_conn_nil_returns;
  try rewrite !atoms_conn_nil_atoms;
  try rewrite !nil_atoms_conn_atoms;
  try rewrite !nil_atoms_conn_returns;
  try rewrite !nil_atoms_conn_Cpres);
  repeat try apply atoms_conn_nil_Spres_sem.

Ltac solve_split:=
  clean_nil;
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
  clean_nil;
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
      try solve [constructor]; clean_nil; try solve_split
    | _ => idtac
   end.

Ltac combine_aux_atom_auto:=
match goal with
| t: C_partial_pres [] |- _ => 
  rewrite (lb_nil_inv t) in *
| _ => idtac
end;
clean_nil;
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
    repeat split;try solve [constructor];  try solve_split
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
    repeat split;try solve [constructor];try solve_split
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

Ltac group_inv :=
  repeat (match goal with
  | E: CForall (@pre_to_semax _ _ _ _) (atoms_conn_Cpres _ _) |- _ =>
      apply atoms_conn_pres_group_inv in E
  | E: CForall (@path_to_semax _ _ _) (Cposts_conn_Cpres _ _) |- _ =>
      apply posts_conn_pres_group_inv in E
  | E: CForall (@post_to_semax _ _ _ _) (Cposts_conn_atoms _ _) |- _ =>
      apply posts_conn_atoms_group_inv in E
  | E: CForall (@post_ret_to_semax _ _ _ _) (Cposts_conn_returns _ _) |- _ =>
      apply posts_conn_returns_group_inv in E
  | E: Forall (atom_to_semax _ _ _) (atoms_conn_atoms _ _) |- _ =>
      apply atoms_conn_atoms_group_inv in E
  | E: Forall (atom_ret_to_semax _ _ _) (atoms_conn_returns _ _) |- _ =>
      apply atoms_conn_returns_group_inv in E
  | _ => idtac
  end).

Lemma copy_iff: forall {P Q}, 
  P <-> Q ->
  P -> (P /\ Q).
Proof.
  tauto.
Qed.

Lemma copy_iff': forall {P Q}, 
  P <-> Q ->
  Q -> (P /\ Q).
Proof.
  tauto.
Qed.

Arguments posts_conn_atoms_conn_returns_assoc {_ _ _ _ _ _ _ _}.
Arguments posts_conn_atoms_conn_atoms_assoc {_ _ _ _ _ _ _ _}.
Arguments posts_conn_atoms_conn_pres_assoc {_ _ _ _ _ _ _ _}.

Ltac destruct_hypos :=
  repeat match goal with
  | E: _ /\ _ |- _ => 
  let n1 := fresh E in
  let n2 := fresh E in
  destruct E as [n1 n2]
  end.

Ltac apply_assoc :=
  repeat match goal with
  | E: CForall (@path_to_semax _ _ _)
      (Cposts_conn_Cpres _ (atoms_conn_Cpres _ _)) |- _ =>
    apply (copy_iff' posts_conn_atoms_conn_pres_assoc) in E
  | E: CForall (@path_to_semax _ _ _)
      (Cposts_conn_Cpres (Cposts_conn_atoms _ _) _) |- _ =>
    apply (copy_iff posts_conn_atoms_conn_pres_assoc) in E
  | E: CForall (@post_to_semax _ _ _ _)
        (Cposts_conn_atoms (Cposts_conn_atoms _ _) _) |- _ =>
    apply (copy_iff' posts_conn_atoms_conn_atoms_assoc) in E
  | E: CForall (@post_to_semax _ _ _ _)
        (Cposts_conn_atoms _ (atoms_conn_atoms _ _)) |- _ =>
    apply (copy_iff posts_conn_atoms_conn_atoms_assoc) in E
  | E: CForall (@post_ret_to_semax _ _ _ _)
        (Cposts_conn_returns _ (atoms_conn_returns _ _)) |- _ =>
    apply (copy_iff posts_conn_atoms_conn_returns_assoc) in E
  | E: CForall (@post_ret_to_semax _ _ _ _)
        (Cposts_conn_returns (Cposts_conn_atoms _ _) _) |- _ =>
    apply (copy_iff' posts_conn_atoms_conn_returns_assoc) in E
  end.

Ltac apply_exclude_nil_cons:=
  repeat match goal with
  | E: _ :: _ = [] \/ _ |- _ =>
    apply (exclude_nil_cons) in E
  end.


Lemma loop_soundness: forall P Q s_res1 s_res2
  (c_res1: C_result s_res1) (c_res2: C_result s_res2),
  s_res_has_path s_res2 -> s_res_has_path s_res1 ->
  split_Semax Delta P Q
    (C_split_loop_refined s_res1 s_res2 c_res1 c_res2) ->
  exists R1 R2,
    ENTAIL Delta, allp_fun_id Delta && P |-- R1 /\
    split_Semax Delta R1 (loop1_ret_assert R2 Q) c_res1 /\
    split_Semax Delta R2 (loop2_ret_assert R1 Q) c_res2
    (* (ENTAIL Delta, allp_fun_id Delta && RA_normal R |-- RA_normal Q /\
    ENTAIL Delta, allp_fun_id Delta && RA_break R |-- RA_break Q /\
    ENTAIL Delta, allp_fun_id Delta && RA_continue R |-- RA_continue Q /\
    (forall vl,
    ENTAIL Delta, allp_fun_id Delta && RA_return R vl |-- RA_return Q vl)) *)
    .
Proof.
  intros P Q s_res1 s_res2. intros c_res1 c_res2.
  intros Hpath Hpath' H.
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



  exists ( EX R:assert, andp R (
  !!
    ( CForall (@pre_to_semax CS Espec Delta R) c_pre1 /\
      CForall (@pre_to_semax CS Espec Delta R) 
        (atoms_conn_Cpres s_atom_normal1 c_pre2)  /\
      CForall (@pre_to_semax CS Espec Delta R) 
        (atoms_conn_Cpres s_atom_continue1 c_pre2) /\
      CForall (@pre_to_semax CS Espec Delta R) 
        (atoms_conn_Cpres s_atom_normal1 
          (add_Q_to_Catoms FF s_atom_continue2))  /\
      CForall (@pre_to_semax CS Espec Delta R) 
        (atoms_conn_Cpres s_atom_continue1 
          (add_Q_to_Catoms FF s_atom_continue2))  /\
      Forall (atom_ret_to_semax Delta R Qr) s_atom_return1 /\
      Forall (atom_to_semax Delta R Qn) s_atom_break1 /\ 
      Forall (atom_to_semax Delta R Qn) 
        (atoms_conn_atoms s_atom_normal1 s_atom_break2) /\
      Forall (atom_to_semax Delta R Qn) 
        (atoms_conn_atoms s_atom_continue1 s_atom_break2) /\
      Forall (atom_ret_to_semax Delta R Qr)    
        (atoms_conn_returns s_atom_normal1 s_atom_return2) /\
      Forall (atom_ret_to_semax Delta R Qr)    
        (atoms_conn_returns s_atom_continue1 s_atom_return2)
      
      ))).


  exists (
    EX R:assert, andp R (
      !!
        ( CForall (@pre_to_semax CS Espec Delta R) c_pre2 /\
          CForall (@pre_to_semax CS Espec Delta R)
              (add_Q_to_Catoms FF s_atom_continue2) /\
          CForall (@pre_to_semax CS Espec Delta R)
              (atoms_conn_Cpres [] c_pre1) /\
          Forall (atom_ret_to_semax Delta R Qr) s_atom_return2 /\
          Forall (atom_to_semax Delta R Qn) s_atom_break2 /\
          Forall (atom_to_semax Delta R Qn) 
              (atoms_conn_atoms [] s_atom_break1) /\
          Forall (atom_ret_to_semax Delta R Qr) 
              (atoms_conn_returns [] s_atom_return1))
  )).

  split.
  { Exists P. apply andp_right. solve_andp.
    apply prop_right. repeat split;auto. }

  apply_assoc. destruct_hypos.
  group_inv.  
  split.

  + unfold loop1_ret_assert.
    repeat split;unfold loop1_ret_assert;unfold_der;auto.
    *
      eapply pre_to_semax_derives_group;
      [|apply pre_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
    *
      (* Search (CForall _ c_post_normal1). *)
      destruct s_pre2,
      s_atom_break2,s_atom_continue2,s_atom_return2;
      try apply exclude_nil_cons in S19;
      try apply exclude_nil_cons in S11;
      try apply exclude_nil_cons in S17;
      try apply exclude_nil_cons in S27;
      try apply exclude_nil_cons in S25;
      try apply exclude_nil_cons in S16;
      try apply exclude_nil_cons in S63;
      try apply exclude_nil_cons in S36;
      [exfalso; apply Hpath; repeat split;auto|..];
      combine_aux_post_auto.
    * 
      (* Search (CForall _ c_post_continue1). *)
      destruct s_pre2,
      s_atom_break2,s_atom_continue2,s_atom_return2;
      try apply exclude_nil_cons in S21;
      try apply exclude_nil_cons in S12;
      try apply exclude_nil_cons in S28;
      try apply exclude_nil_cons in S13;
      try apply exclude_nil_cons in S49;
      try apply exclude_nil_cons in S62;
      try apply exclude_nil_cons in S37;
      [exfalso; apply Hpath; repeat split;auto|..];
      combine_aux_post_auto.
    *
      eapply atom_to_semax_derives_pre_group;
      [|apply atom_to_semax_sem_group].
      merge_Q1. apply prop_right.
      group_inv.
      (* Search (Forall _ s_atom_normal1). *)
      destruct s_pre2,
      s_atom_break2,s_atom_continue2,s_atom_return2;
      try apply exclude_nil_cons in H6;
      try apply exclude_nil_cons in H8;
      try apply exclude_nil_cons in H0;
      try apply exclude_nil_cons in H2;
      [exfalso; apply Hpath; repeat split;auto|..];
      combine_aux_atom_auto.
    *
      eapply atom_to_semax_derives_pre_group;
      [|apply atom_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
    * 
      eapply atom_to_semax_derives_pre_group;
      [|apply atom_to_semax_sem_group].
      merge_Q1. apply prop_right.
      group_inv.
      (* Search (Forall _ s_atom_continue1). *)
      destruct s_pre2,
      s_atom_break2,s_atom_continue2,s_atom_return2;
      try apply exclude_nil_cons in H7;
      try apply exclude_nil_cons in H9;
      try apply exclude_nil_cons in H3;
      try apply exclude_nil_cons in H1;
      [exfalso; apply Hpath; repeat split;auto|..];
      combine_aux_atom_auto.
    * 
      eapply atom_return_to_semax_derives_pre_group;
      [|apply atom_return_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
  
  + unfold loop2_ret_assert.
    repeat split;unfold loop2_ret_assert;unfold_der;auto.
    *
      eapply pre_to_semax_derives_group;
      [|apply pre_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
    *
      (* Search (CForall _ c_post_normal2). *)
      assert (s_atom_normal1 = [] \/ CForall
        (@post_to_semax CS Espec Delta
          (EX R, R &&
          !! (CForall (@pre_to_semax CS Espec Delta R)
                (atoms_conn_Cpres s_atom_normal1 c_pre2) /\
              CForall (@pre_to_semax CS Espec Delta R)
                (atoms_conn_Cpres s_atom_normal1 (add_Q_to_Catoms FF s_atom_continue2)) /\
              Forall (atom_to_semax Delta R Qn)
                (atoms_conn_atoms s_atom_normal1 s_atom_break2) /\
              Forall (atom_ret_to_semax Delta R Qr)
                (atoms_conn_returns s_atom_normal1 s_atom_return2))))
          c_post_normal2).
      {
        destruct s_atom_normal1;auto. right. 
        (* Search s_atom_normal1 c_post_normal2. *)
        clear - S57 S59 S23 S15 Hpath.
        destruct s_pre2,
        s_atom_break2, s_atom_continue2,s_atom_return2;
        try (apply exclude_nil_cons in S57);
        try (apply exclude_nil_cons in S59);
        try (apply exclude_nil_cons in S23);
        try (apply exclude_nil_cons in S15);
        [exfalso; apply Hpath; repeat split;auto|..
        (* |
          eapply post_to_semax_derives_group;
          [|eapply post_to_semax_conj_rule_group;
            [apply S60|
              eapply post_to_semax_conj_rule_group;
              [apply S62|
              eapply post_to_semax_conj_rule_group;
              [apply S24|apply S15]]]];
              try (apply remove_entail);
              merge_Q4; apply prop_right;
              repeat split;try solve [constructor];clean_nil;solve_split *)
        ];combine_aux_post_auto.
      }

      assert (s_atom_continue1 = [] \/ CForall 
      (@post_to_semax CS Espec Delta
        (EX R, R &&
          !! (CForall (@pre_to_semax CS Espec Delta R)
            (atoms_conn_Cpres s_atom_continue1 c_pre2) /\
          CForall (@pre_to_semax CS Espec Delta R)
            (atoms_conn_Cpres s_atom_continue1 (add_Q_to_Catoms FF s_atom_continue2)) /\
          Forall (atom_to_semax Delta R Qn)
            (atoms_conn_atoms s_atom_continue1 s_atom_break2) /\
          Forall (atom_ret_to_semax Delta R Qr)
            (atoms_conn_returns s_atom_continue1 s_atom_return2))))
          c_post_normal2
      ).
      {
        destruct s_atom_continue1;auto. right. 
        (* Search s_atom_continue1 c_post_normal2. *)
        clear - S24 S16 S56 S58 Hpath.
        destruct s_pre2,
        s_atom_break2, s_atom_continue2,s_atom_return2;
        try (apply exclude_nil_cons in S24);
        try (apply exclude_nil_cons in S16);
        try (apply exclude_nil_cons in S56);
        try (apply exclude_nil_cons in S58);
        [exfalso; apply Hpath; repeat split;auto|..];combine_aux_post_auto.
      }
      clear - H H0 S29 S13 S20 Hpath'.
      destruct s_pre1, s_atom_normal1,
      s_atom_break1, s_atom_continue1, s_atom_return1;
        try (apply exclude_nil_cons in H);
        try (apply exclude_nil_cons in H0);
        try (apply exclude_nil_cons in S13);
        try (apply exclude_nil_cons in S29);
        try (apply exclude_nil_cons in S20);
        [exfalso; apply Hpath'; repeat split;auto|..];
      combine_aux_post_auto.

    * apply add_Q_to_Cposts_inv. auto.

    * eapply atom_to_semax_derives_pre_group;
      [|apply atom_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.

    * 
      eapply atom_to_semax_derives_pre_group;
      [|apply atom_to_semax_sem_group].
      merge_Q1. apply prop_right.
      (* TODO: factor out this proof *)
      clear - H0. induction s_atom_continue2;auto. destruct a.
      simpl in H0.
      destruct H0. apply IHs_atom_continue2 in H0.
      constructor;auto.
    
    * eapply atom_return_to_semax_derives_pre_group;
      [|apply atom_return_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
    
  }

  { destruct s_atom_continue1, s_atom_normal1.
    2:{ simpl in H. inversion H. }
    2:{ simpl in H. inversion H. }
    2:{ simpl in H. inversion H. }
    destruct c_res1 as [
    c_pre1 c_path1 c_post_normal1 c_post_break1
    c_post_continue1 c_post_return1] eqn:Ec1,
    c_res2 as [
    c_pre2 c_path2 c_post_normal2 c_post_break2
    c_post_continue2 c_post_return2] eqn:Ec2.
    destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
    destruct_FForalls.

    destruct Q as [ Qn Qb Qc Qr];unfold_der.


    exists ( EX R:assert, andp R (
      !!
        ( CForall (@pre_to_semax CS Espec Delta R) c_pre1 /\
          CForall (@pre_to_semax CS Espec Delta R) 
            (atoms_conn_Cpres [] c_pre2)  /\
          CForall (@pre_to_semax CS Espec Delta R) 
            (atoms_conn_Cpres [] c_pre2) /\
          CForall (@pre_to_semax CS Espec Delta R) 
            (atoms_conn_Cpres [] 
              (add_Q_to_Catoms FF s_atom_continue2))  /\
          CForall (@pre_to_semax CS Espec Delta R) 
            (atoms_conn_Cpres [] 
              (add_Q_to_Catoms FF s_atom_continue2))  /\
          Forall (atom_ret_to_semax Delta R Qr) s_atom_return1 /\
          Forall (atom_to_semax Delta R Qn) s_atom_break1 /\ 
          Forall (atom_to_semax Delta R Qn) 
            (atoms_conn_atoms [] s_atom_break2) /\
          Forall (atom_to_semax Delta R Qn) 
            (atoms_conn_atoms [] s_atom_break2) /\
          Forall (atom_ret_to_semax Delta R Qr)    
            (atoms_conn_returns [] s_atom_return2) /\
          Forall (atom_ret_to_semax Delta R Qr)    
            (atoms_conn_returns [] s_atom_return2)
      
      ))).


    exists (
      EX R:assert, andp R (
        !!
          ( CForall (@pre_to_semax CS Espec Delta R) c_pre2 /\
            CForall (@pre_to_semax CS Espec Delta R)
                (add_Q_to_Catoms FF s_atom_continue2) /\
            CForall (@pre_to_semax CS Espec Delta R)
                (atoms_conn_Cpres (a :: s_atom_normal2) c_pre1) /\
            Forall (atom_ret_to_semax Delta R Qr) s_atom_return2 /\
            Forall (atom_to_semax Delta R Qn) s_atom_break2 /\
            Forall (atom_to_semax Delta R Qn) 
                (atoms_conn_atoms (a :: s_atom_normal2) s_atom_break1) /\
            Forall (atom_ret_to_semax Delta R Qr) 
                (atoms_conn_returns (a :: s_atom_normal2) s_atom_return1))
    )).

  split.
  { Exists P. apply andp_right. solve_andp.
    apply prop_right. repeat split;auto. }

  apply_assoc. destruct_hypos.
  group_inv.  
  split.

  + unfold loop1_ret_assert.
    repeat split;unfold loop1_ret_assert;unfold_der;auto.
    *
      eapply pre_to_semax_derives_group;
      [|apply pre_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
    *
      (* Search (CForall _ c_post_normal1). *)
      clear - Hpath Hpath' S61 S36 S17 S25 S27 S11 S19.


      assert (CForall (@post_to_semax CS Espec Delta
      (EX R:assert, andp R (
        !!
          ( CForall (@pre_to_semax CS Espec Delta R)
                (atoms_conn_Cpres (a :: s_atom_normal2) c_pre1) /\
            Forall (atom_to_semax Delta R Qn) 
                (atoms_conn_atoms (a :: s_atom_normal2) s_atom_break1) /\
            Forall (atom_ret_to_semax Delta R Qr) 
                (atoms_conn_returns (a :: s_atom_normal2) s_atom_return1))
      ))) c_post_normal1).
      { destruct s_pre1, s_atom_break1, s_atom_return1;
        [exfalso; apply Hpath'; repeat split;auto|..];
        try apply exclude_nil_cons in S25;
        try apply exclude_nil_cons in S17;
        try apply exclude_nil_cons in S61;
        combine_aux_post_auto.
      }
      clear S25 S17 S61.
      (* Search (CForall _ c_post_normal1). *)
      destruct s_pre2,
      s_atom_break2,s_atom_continue2,s_atom_return2;
      try apply exclude_nil_cons in S19;
      try apply exclude_nil_cons in S11;
      try apply exclude_nil_cons in H;
      try apply exclude_nil_cons in S27;
      try apply exclude_nil_cons in S36;
      combine_aux_post_auto.
    *
      (* Search (CForall _ c_post_continue1). *)
      clear - Hpath Hpath' S60 S37 S47 S14 S28 S12 S21.


      assert (CForall (@post_to_semax CS Espec Delta
      (EX R:assert, andp R (
        !!
          ( CForall (@pre_to_semax CS Espec Delta R)
                (atoms_conn_Cpres (a :: s_atom_normal2) c_pre1) /\
            Forall (atom_to_semax Delta R Qn) 
                (atoms_conn_atoms (a :: s_atom_normal2) s_atom_break1) /\
            Forall (atom_ret_to_semax Delta R Qr) 
                (atoms_conn_returns (a :: s_atom_normal2) s_atom_return1))
      ))) c_post_continue1).
      { destruct s_pre1, s_atom_break1, s_atom_return1;
        [exfalso; apply Hpath'; repeat split;auto|..];
        try apply exclude_nil_cons in S14;
        try apply exclude_nil_cons in S47;
        try apply exclude_nil_cons in S60;
        combine_aux_post_auto.
      }
      clear S14 S47 S60.
      destruct s_pre2,
      s_atom_break2,s_atom_continue2,s_atom_return2;
      try apply exclude_nil_cons in S28;
      try apply exclude_nil_cons in S37;
      try apply exclude_nil_cons in H;
      try apply exclude_nil_cons in S12;
      try apply exclude_nil_cons in S21;
      combine_aux_post_auto.

    *
      eapply atom_to_semax_derives_pre_group;
      [|apply atom_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
    *
      eapply atom_return_to_semax_derives_pre_group;
      [|apply atom_return_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
  
  + unfold loop2_ret_assert.
    repeat split;unfold loop2_ret_assert;unfold_der;auto.
    *
      eapply pre_to_semax_derives_group;
      [|apply pre_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.
    *
      (* Search (CForall _ c_post_normal2). *)
      clear - Hpath' S13 S20 S29.
      destruct s_pre1, s_atom_break1, s_atom_return1;
        try (apply exclude_nil_cons in S13);
        try (apply exclude_nil_cons in S20);
        try (apply exclude_nil_cons in S29);
        [exfalso; apply Hpath'; repeat split;auto|..];
      combine_aux_post_auto.

    * apply add_Q_to_Cposts_inv. auto.

    * eapply atom_to_semax_derives_pre_group;
      [|apply atom_to_semax_sem_group].
      merge_Q1. apply prop_right.
      group_inv.
      clear - Hpath' H1 H4 H5.
      destruct s_pre1, s_atom_break1, s_atom_return1;
        try (apply exclude_nil_cons in H1);
        try (apply exclude_nil_cons in H4);
        try (apply exclude_nil_cons in H5);
        [exfalso; apply Hpath'; repeat split;auto|..];
      combine_aux_atom_auto.

    * 
      eapply atom_to_semax_derives_pre_group;
      [|apply atom_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.

    *
      eapply atom_to_semax_derives_pre_group;
      [|apply atom_to_semax_sem_group].
      merge_Q1. apply prop_right.
      (* TODO: factor out this proof *)
      clear - H0. induction s_atom_continue2;auto. destruct a.
      simpl in H0.
      destruct H0. apply IHs_atom_continue2 in H0.
      constructor;auto.
    
    * eapply atom_return_to_semax_derives_pre_group;
      [|apply atom_return_to_semax_sem_group].
      merge_Q1. apply prop_right. auto.

  }
Qed.


Lemma if_soundness: 
forall P Q e s_res1 s_res2
  (c_res1: C_result s_res1) (c_res2: C_result s_res2),
  s_res_has_path s_res2 -> s_res_has_path s_res1 ->
  split_Semax Delta P Q
    (C_split_ifthenelse e s_res1 s_res2 c_res1 c_res2) ->
  ENTAIL Delta, allp_fun_id Delta && P |-- 
    (!! ((bool_type (typeof e)) = true)) &&
   (tc_expr Delta (Eunop Onotbool e (Ctypes.Tint I32 Signed noattr))) && P /\
  split_Semax Delta (P && local (liftx (typed_true (typeof e)) (eval_expr e))) Q c_res1 /\
  split_Semax Delta (P && local (liftx (typed_false (typeof e)) (eval_expr e))) Q c_res2.
Proof.
  intros P Q e s_res1 s_res2. intros c_res1 c_res2.
  intros Hpath Hpath' H.
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
  destruct c_res1 as [
    c_pre1 c_path1 c_post_normal1 c_post_break1
    c_post_continue1 c_post_return1] eqn:Ec1,
    c_res2 as [
    c_pre2 c_path2 c_post_normal2 c_post_break2
    c_post_continue2 c_post_return2] eqn:Ec2.
  destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  destruct_FForalls.

  split;[|split].
  + apply andp_right;try solve_andp.
    simpl in Hpath'.
    eapply if_gen_tc with (Q0:=Q) (b:=true);[apply Hpath'|..];auto.
    apply S1.
  + repeat split;auto.
    * apply pre_to_semax_if_true_inv_group;auto.
    * apply atom_to_semax_if_true_inv_group;auto.
    * apply atom_to_semax_if_true_inv_group;auto.
    * apply atom_to_semax_if_true_inv_group;auto.
    * apply atom_ret_to_semax_if_true_inv_group;auto.
  + repeat split;auto.
    * apply pre_to_semax_if_false_inv_group;auto.
    * apply atom_to_semax_if_false_inv_group;auto.
    * apply atom_to_semax_if_false_inv_group;auto.
    * apply atom_to_semax_if_false_inv_group;auto.
    * apply atom_ret_to_semax_if_false_inv_group;auto.
Qed.

Lemma skip_sound: forall P Q,
  split_Semax Delta P Q (C_split Sskip (Cskip)) ->
  semax Delta P Clight.Sskip Q.
Proof.
  intros.
  simpl.
  simpl in H.
  destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  inversion S7;subst.
  simpl in H1.
  apply semax_skip_inv in H1.
  rewrite normal_split_assert_elim in H1.
  eapply semax_pre';[apply H1|].
  destruct Q as [Qn Qb Qc Qr];unfold_der.
  eapply semax_noreturn_inv with (
    Post:= Build_ret_assert Qn Qb Qc (fun _ => FF)
  );auto.
  eapply semax_nocontinue_inv with (
    Post:= Build_ret_assert Qn Qb FF (fun _ => FF)
  );auto.
  eapply semax_nobreak_inv with (
    Post:= Build_ret_assert Qn FF FF (fun _ => FF)
  );auto.
  constructor.
Qed.

Lemma assign_sound: forall e1 e2 P Q,
  split_Semax Delta P Q (C_split (Sassign e1 e2) (Cassign e1 e2)) ->
  semax Delta P (Clight.Sassign e1 e2) Q.
Proof.
  intros.
  simpl.
  simpl in H.
  destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  inversion S7;subst.
  simpl in H1.
  apply semax_seq_inv in H1. destruct H1 as [Q' [H1 H3]].
  apply semax_skip_inv in H3.
  destruct Q as [Qn Qb Qc Qr];unfold_der;
  unfold normal_split_assert in *.
  eapply semax_noreturn_inv with (
    Post:= Build_ret_assert Qn Qb Qc (fun _ => TT)
  );auto.
  eapply semax_nocontinue_inv with (
    Post:= Build_ret_assert Qn Qb TT (fun _ => TT)
  );auto.
  eapply semax_nobreak_inv with (
    Post:= Build_ret_assert Qn TT TT (fun _ => TT)
  );auto.
  eapply semax_conseq;[..|apply H1]; try solve [intros;solve_andp];auto.
Qed.


Lemma set_sound: forall e1 e2 P Q,
  split_Semax Delta P Q (C_split (Sset e1 e2) (Cset e1 e2)) ->
  semax Delta P (Clight.Sset e1 e2) Q.
Proof.
  intros.
  simpl.
  simpl in H.
  destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  inversion S7;subst.
  simpl in H1.
  apply semax_seq_inv in H1. destruct H1 as [Q' [H1 H3]].
  apply semax_skip_inv in H3.
  destruct Q as [Qn Qb Qc Qr];unfold_der;
  unfold normal_split_assert in *.
  eapply semax_noreturn_inv with (
    Post:= Build_ret_assert Qn Qb Qc (fun _ => TT)
  );auto.
  eapply semax_nocontinue_inv with (
    Post:= Build_ret_assert Qn Qb TT (fun _ => TT)
  );auto.
  eapply semax_nobreak_inv with (
    Post:= Build_ret_assert Qn TT TT (fun _ => TT)
  );auto.
  eapply semax_conseq;[..|apply H1]; try solve [intros;solve_andp];auto.
Qed.


Lemma call_sound: forall id e ret P Q,
  split_Semax Delta P Q (C_split (Scall id e ret) (Ccall id e ret)) ->
  semax Delta P (Clight.Scall id e ret) Q.
Proof.
  intros.
  simpl.
  simpl in H.
  destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  inversion S7;subst.
  simpl in H1.
  apply semax_seq_inv in H1. destruct H1 as [Q' [H1 H3]].
  apply semax_skip_inv in H3.
  destruct Q as [Qn Qb Qc Qr];unfold_der;
  unfold normal_split_assert in *.
  eapply semax_noreturn_inv with (
    Post:= Build_ret_assert Qn Qb Qc (fun _ => TT)
  );auto.
  eapply semax_nocontinue_inv with (
    Post:= Build_ret_assert Qn Qb TT (fun _ => TT)
  );auto.
  eapply semax_nobreak_inv with (
    Post:= Build_ret_assert Qn TT TT (fun _ => TT)
  );auto.
  eapply semax_conseq;[..|apply H1]; try solve [intros;solve_andp];auto.
Qed.

Lemma break_soundness: forall P Q,
split_Semax Delta P Q (C_split Sbreak Cbreak) ->
semax Delta P Clight.Sbreak Q.
Proof.
  intros.
  simpl.
  simpl in H.
  destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  inversion S8;subst.
  simpl in H1.
  apply semax_skip_inv in H1.
  rewrite normal_split_assert_elim in H1.
  eapply semax_pre';[apply H1|].
  constructor.
Qed.


Lemma continune_soundness: forall P Q,
split_Semax Delta P Q (C_split Scontinue Ccontinue) ->
semax Delta P Clight.Scontinue Q.
Proof.
  intros.
  simpl.
  simpl in H.
  destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  inversion S9;subst.
  simpl in H1.
  apply semax_skip_inv in H1.
  rewrite normal_split_assert_elim in H1.
  eapply semax_pre';[apply H1|].
  constructor.
Qed.


Lemma return_soundness: forall P Q v,
split_Semax Delta P Q (C_split (Sreturn v) (Creturn v)) ->
semax Delta P (Clight.Sreturn v) Q.
Proof.
  intros.
  simpl.
  simpl in H.
  destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  inversion S10;subst.
  simpl in H1.
  apply semax_return_inv in H1.
  destruct Q.
  unfold return_split_assert in *.  unfold_der.
  eapply semax_pre';[|apply semax_return].
  auto.
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
    intros. apply skip_sound. auto.

  - (* exgiven *)
    intros. simpl in H0.
    pose proof ex_given_sound _ _ _ _ _ _ H0.
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
    intros. apply assign_sound. auto.

  - (* call *)
    intros. apply call_sound. auto.

  - (* set *)
    intros. apply set_sound. auto.

  - (* ifthenelse *)
    intros. simpl. simpl in H.
    apply if_soundness in H.
    2:{ apply S_split_has_path. }
    2:{ apply S_split_has_path. }
    destruct H as [E1 [E2 E3]].
    eapply semax_pre';[apply E1|].
    apply semax_ifthenelse;auto.

  - (* loop *)
    intros. simpl.
    simpl in H.
    apply loop_soundness in H.
    2:{ apply S_split_has_path. }
    2:{ apply S_split_has_path. }
    destruct H as [R1 [R2 [H1 [H2 H3]]]].
    eapply semax_pre'.
    { apply H1. }
    apply semax_loop with (Q':=R2).
    { apply IHc_stm1. auto. }
    { apply IHc_stm2. auto. }

  - (* break *)
    intros. apply break_soundness. auto.

  - (* continue *)
    intros. apply continune_soundness. auto.

  - (* return *)
    intros. apply return_soundness. auto.

Qed.


End Soundness.