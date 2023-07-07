Require Export Csplit.AClight.
Require Import VST.floyd.proofauto.
Require Import Csplit.strong.
Require Import Csplit.semantics.

Section SemanticsProofs.

Local Open Scope logic.

Context {CS: compspecs} {Espec: OracleKind} (Delta: tycontext).


Lemma pre_to_semax_derives: forall P Q s_pre 
  (c_pre: C_partial_pre s_pre),
  ENTAIL Delta, ((allp_fun_id Delta) && Q) |--  P ->
  pre_to_semax Delta P c_pre ->
  pre_to_semax Delta Q c_pre.
Proof.
  intros.
  induction c_pre.
  + simpl. eapply semax_pre';[..|apply H0].
    auto.
  (* + simpl in *. auto. *)
Qed.

Lemma pre_to_semax_derives_weak: forall P Q s_pre 
  (c_pre: C_partial_pre s_pre),
  Q |--  P ->
  pre_to_semax Delta P c_pre ->
  pre_to_semax Delta Q c_pre.
Proof.
  intros.
  eapply pre_to_semax_derives;[|apply H0].
  eapply derives_trans;[|apply H];solve_andp.
Qed.

Lemma post_to_semax_derives: forall P Q s_post
  (c_post: C_partial_post s_post),
  ENTAIL Delta, Q |--  P ->
  post_to_semax Delta Q c_post ->
  post_to_semax Delta P c_post.
Proof.
  intros. induction c_post.
  + simpl in H0. simpl.
    eapply semax_conseq with (P':=pre)(R':= normal_split_assert Q);auto;
    unfold normal_split_assert, RA_normal, RA_break, RA_continue, RA_return;
    intros;try solve_andp.
    { eapply derives_trans;[|apply H]. solve_andp. }
  (* + simpl in *. auto. *)
Qed.

Lemma post_ret_to_semax_derives: forall P Q s_post
  (c_post: C_partial_post_ret s_post),
  (forall v, ENTAIL Delta, Q v |--  P v) ->
  post_ret_to_semax Delta Q c_post ->
  post_ret_to_semax Delta P c_post.
Proof.
  intros. induction c_post.
  + simpl in H0. simpl.
    eapply semax_conseq with (P':=pre)(R':= return_split_assert Q);auto;
    unfold return_split_assert, RA_normal, RA_break, RA_continue, RA_return;
    intros;try solve_andp.
    { eapply derives_trans;[|apply H]. solve_andp. }
  (* + simpl in *. auto. *)
Qed.

Lemma atom_to_semax_derives: forall P1 P2 Q1 Q2 a,
  P2 |-- P1 ->
  ENTAIL Delta, Q1 |-- Q2 ->
  atom_to_semax Delta P1 Q1 a ->
  atom_to_semax Delta P2 Q2 a.
Proof.
  intros. destruct a;simpl.
  eapply semax_conseq with (P':=P1)(R':=normal_split_assert Q1);auto;
  unfold normal_split_assert, RA_normal, RA_break, RA_continue, RA_return;
  intros;try solve_andp.
  - eapply derives_trans;[|apply H]. solve_andp. 
  - eapply derives_trans;[|apply H0]. solve_andp.
Qed.

Lemma atom_return_to_semax_derives: forall P1 P2 Q1 Q2 a,
  P2 |-- P1 ->
  (forall v, ENTAIL Delta, Q1 v  |-- Q2 v ) ->
  atom_ret_to_semax Delta P1 Q1 a ->
  atom_ret_to_semax Delta P2 Q2 a.
Proof.
  intros. destruct a as [p r].
  eapply semax_conseq with (P':=P1)(R':=return_split_assert Q1);
  unfold return_split_assert;auto;
  unfold RA_normal, RA_break, RA_continue, RA_return;
  intros;try solve_andp.
  - eapply derives_trans;[|apply H]. solve_andp.
  - eapply derives_trans;[|apply H0]. solve_andp.
Qed.

Lemma pre_to_semax_sem: forall (s_pre: S_partial_pre)
  (c_pre: C_partial_pre s_pre),
  (pre_to_semax Delta
        (EX Q : assert,
          !! (pre_to_semax Delta Q c_pre) && Q)) 
      c_pre.
Proof.
  intros.
  induction c_pre.
  - unfold pre_to_semax. apply semax_extract_exists.
    intros Q.
    apply semax_extract_prop.
    intros. auto.
  (* - intros x. specialize (H x).
    eapply pre_to_semax_derives. 2:{ apply H. }
    Intros Q. Exists Q.
    apply andp_right.
    + apply prop_right. apply H0.
    + solve_andp. *)
Qed.


Lemma post_to_semax_reverse: forall { s_post }
  (c_post: C_partial_post s_post) atom R,
  post_to_semax Delta R (Cpost_conn_atom c_post atom) ->
  post_to_semax Delta (EX Q, Q && !! ( atom_to_semax Delta Q R atom)) c_post.
Proof.
  intros. destruct atom.
  induction c_post.
  - simpl in H.
    apply path_to_statement_app in H.
    apply semax_seq_inv in H.
    destruct H as [Q [? ?]].
    eapply post_to_semax_derives.
    2: { simpl. apply H. }
    Exists Q.
    apply andp_right.
    + solve_andp.
    + apply prop_right. auto.
  (* - simpl. intros. simpl in H. specialize (H a). apply H0 in H. auto. *)
Qed.

Lemma path_conn_to_semax_reverse_simple: forall { s_pre }
  (c_pre: C_partial_pre s_pre) a1,
  path_to_semax Delta (add_P_to_Cpre a1 c_pre) ->
    pre_to_semax Delta a1 c_pre.
Proof.
  intros.
  induction c_pre.
  - simpl in H. simpl. auto.
  (* - simpl in H0, H. destruct s.
    simpl in H. simpl. auto. *)
Qed.


(* -------------------------------------------------
   Assertion Derivation 
   for paths/partial paths/atoms 
--------------------------------------------------- *)

Lemma atom_return_to_semax_derives_pre: forall p P1 P2 Q,
P1 |-- P2 ->
atom_ret_to_semax Delta P2 Q p ->
atom_ret_to_semax Delta P1 Q p.
Proof.
 intros.
 eapply atom_return_to_semax_derives.
 { apply H. }
 { intros. solve_andp. }
 { auto. }
Qed.

Lemma atom_return_to_semax_derives_post: forall p P Q1 Q2,
(forall v, ENTAIL Delta, Q1 v |-- Q2 v) ->
atom_ret_to_semax Delta P Q1 p ->
atom_ret_to_semax Delta P Q2 p.
Proof.
 intros.
 eapply atom_return_to_semax_derives.
 { apply derives_refl. }
 { intros. apply H. }
 { auto. }
Qed.

Lemma atom_return_to_semax_derives_pre_group: forall P1 P2 Q atoms,
  P1 |-- P2 ->
  Forall (atom_ret_to_semax Delta P2 Q) atoms ->
  Forall (atom_ret_to_semax Delta P1 Q) atoms.
Proof. 
  intros.
  induction H0.
  - constructor.
  - constructor;auto. eapply atom_return_to_semax_derives_pre.
    apply H. auto.
Qed.

Lemma pre_to_semax_derives_group_weak: forall P1 P2 
  s_pres (c_pres : C_partial_pres s_pres),
  P1 |-- P2 ->
  CForall (@pre_to_semax CS Espec Delta P2) c_pres ->
  CForall (@pre_to_semax CS Espec Delta P1) c_pres.
Proof. 
  intros.
  induction c_pres.
  - constructor.
  - destruct H0. constructor;auto. eapply pre_to_semax_derives_weak.
    apply H. auto.
Qed.


Lemma pre_to_semax_derives_group: forall P1 P2
  s_pres (c_pres : C_partial_pres s_pres),
  ENTAIL Delta, ((allp_fun_id Delta) && P1) |--  P2 ->
  CForall (@pre_to_semax CS Espec Delta P2) c_pres ->
  CForall (@pre_to_semax CS Espec Delta P1) c_pres.
Proof. 
  intros.
  induction c_pres.
  - constructor.
  - destruct H0. constructor;auto. eapply pre_to_semax_derives.
    apply H. auto.
Qed.

Lemma post_to_semax_derives_group: forall Q1 Q2
  s_posts (c_posts : C_partial_posts s_posts),
  ENTAIL Delta, Q1 |-- Q2  ->
  CForall (@post_to_semax CS Espec Delta Q1) c_posts ->
  CForall (@post_to_semax CS Espec Delta Q2) c_posts.
Proof. 
  intros.
  induction c_posts.
  - constructor.
  - destruct H0. constructor;auto.
    eapply post_to_semax_derives.
    apply H. auto.
Qed.

Lemma post_ret_to_semax_derives_group: forall Q1 Q2
  s_posts (c_posts : C_partial_post_rets s_posts),
  (forall v, ENTAIL Delta, Q1 v |-- Q2 v) ->
  CForall (@post_ret_to_semax CS Espec Delta Q1) c_posts ->
  CForall (@post_ret_to_semax CS Espec Delta Q2) c_posts.
Proof. 
  intros.
  induction c_posts.
  - constructor.
  - destruct H0. constructor;auto.
    eapply post_ret_to_semax_derives.
    apply H. auto.
Qed.

Lemma atom_to_semax_derives_pre: forall p P1 P2 Q,
  P1 |-- P2 ->
  atom_to_semax Delta P2 Q p ->
  atom_to_semax Delta P1 Q p.
Proof.
  intros.
  eapply atom_to_semax_derives.
  - apply H.
  - solve_andp.
  - auto.
Qed.

Lemma atom_to_semax_derives_pre_group: forall P1 P2 Q atoms,
  P1 |-- P2 ->
  Forall (atom_to_semax Delta P2 Q) atoms ->
  Forall (atom_to_semax Delta P1 Q) atoms.
Proof. 
  intros.
  eapply Forall_forall.
  intros. eapply atom_to_semax_derives_pre.
  apply H. eapply Forall_forall in H0. apply H0. auto.
Qed.

Lemma atom_to_semax_derives_post: forall p P Q1 Q2,
  ENTAIL Delta, Q1 |-- Q2 ->
  atom_to_semax Delta P Q1 p ->
  atom_to_semax Delta P Q2 p.
Proof.
  intros.
  eapply atom_to_semax_derives.
  - apply derives_refl.
  - apply H.
  - auto.
Qed.

Lemma atom_to_semax_derives_post_group: forall p P Q1 Q2,
  ENTAIL Delta, Q1 |-- Q2 ->
  Forall (atom_to_semax Delta P Q1) p ->
  Forall (atom_to_semax Delta P Q2) p.
Proof.
  intros. induction p.
  - constructor.
  - inv H0. apply IHp in H4.
    constructor; auto.
    eapply atom_to_semax_derives_post;[|apply H3].
    auto.
Qed.

Lemma atom_return_to_semax_derives_post_group: 
forall p P Q1 Q2,
  (forall v, ENTAIL Delta, Q1 v|-- Q2 v) ->
  Forall (atom_ret_to_semax Delta P Q1) p ->
  Forall (atom_ret_to_semax Delta P Q2) p.
Proof.
  intros. induction p.
  - constructor.
  -  inv H0. apply IHp in H4.
    constructor; auto.
    eapply atom_return_to_semax_derives_post;[|apply H3].
    auto.
Qed.



(*********************)
(* Conjunction Rules *)
(*********************)

(* Single conjunction rule *)

Lemma post_to_semax_conj_rule: forall Q1 Q2 s_post
  (c_post : C_partial_post s_post),
post_to_semax Delta Q1 c_post ->
post_to_semax Delta Q2 c_post ->
post_to_semax Delta (Q1 && Q2) c_post.
Proof.
  intros.
  induction c_post.
  - simpl in *.
    eapply semax_conseq.
    6: { eapply semax_conj_rule with 
          (Q1:= normal_split_assert Q1) 
          (Q2:= normal_split_assert Q2).
        apply H. apply H0. }
    { solve_andp. }
    { solve_andp. }
    { solve_andp. }
    { solve_andp. }
    { intros. solve_andp. }
  (* - simpl in *. auto. *)
Qed.


Lemma atom_to_semax_conj_rule: forall P Q1 Q2 atom,
  atom_to_semax Delta P Q1 atom ->
  atom_to_semax Delta P Q2 atom ->
  atom_to_semax Delta P (Q1 && Q2) atom.
Proof.
  intros. destruct atom. unfold atom_to_semax in *.
  eapply semax_conseq.
  6: { eapply semax_conj_rule with 
  (Q1:= normal_split_assert Q1) 
  (Q2:= normal_split_assert Q2).
    apply H. apply H0. }
  { solve_andp. }
  { solve_andp. }
  { solve_andp. }
  { solve_andp. }
  { intros. solve_andp. }
Qed.


(* Grouped conjunction rule *)

Lemma post_to_semax_conj_rule_group: forall Q1 Q2 s_posts
  (c_posts : C_partial_posts s_posts),
CForall (@post_to_semax  CS Espec Delta Q1) c_posts ->
CForall (@post_to_semax  CS Espec Delta Q2) c_posts ->
CForall (@post_to_semax  CS Espec Delta (Q1 && Q2)) c_posts.
Proof.
  intros.
  induction c_posts.
  - constructor.
  - destruct H. destruct H0.
    specialize (IHc_posts H1 H2).
    constructor;auto.
    apply post_to_semax_conj_rule;auto.
Qed.


Lemma atom_to_semax_conj_rule_group: forall P Q1 Q2 atoms,
  Forall (atom_to_semax Delta P Q1) atoms ->
  Forall (atom_to_semax Delta P Q2) atoms ->
  Forall (atom_to_semax Delta P (Q1 && Q2)) atoms.
Proof.
  intros. induction atoms;auto.
  inversion H;subst.
  inversion H0;subst.
  specialize (IHatoms H4 H6).
  pose proof atom_to_semax_conj_rule _ _ _ _ H3 H5.
  constructor;auto.
Qed.


(***********************************)
(* Inversion Lemmas (Part 2) *******)
(***********************************)

Lemma pre_to_semax_sem_group: forall (s_pres: S_partial_pres)
  (c_pres: C_partial_pres s_pres),
  (CForall (@pre_to_semax  CS Espec Delta
        (EX Q, Q && !! (CForall (@pre_to_semax  CS Espec Delta Q) c_pres))) 
      c_pres).
Proof.
  intros.
  induction c_pres.
  - constructor.
  - split;auto.
    + pose proof pre_to_semax_sem _ r'.
      eapply pre_to_semax_derives;[|apply H].
      Intros Q. Exists Q. apply andp_right.
      apply prop_right;auto. destruct H0. auto. solve_andp.
    + eapply pre_to_semax_derives_group;[|apply IHc_pres].
      Intros Q. Exists Q. apply andp_right. solve_andp.
      apply prop_right;auto. destruct H. auto.
Qed.


Lemma atom_to_semax_sem: forall x  R,
 (atom_to_semax Delta
        (EX Q : assert,
          !! (atom_to_semax Delta Q R x) && Q)) R
      x.
Proof.
  intros. destruct x.
  apply semax_extract_exists. intros Q.
  apply semax_extract_prop.
  intros. auto.
Qed.
  
Lemma atom_return_to_semax_sem: forall x R,
 (atom_ret_to_semax Delta
        (EX Q : assert,
          !! (atom_ret_to_semax Delta Q R x) && Q)) R
      x.
Proof.
  intros. destruct x as [p v].
  apply semax_extract_exists. intros Q.
  apply semax_extract_prop.
  intros. auto.
Qed.


Lemma atom_to_semax_sem_group: forall xs R,
 Forall (atom_to_semax Delta (EX Q : assert, !! Forall (atom_to_semax Delta Q R) xs && Q) R) xs.
Proof.
  intros. induction xs;auto.
  - pose proof atom_to_semax_sem a R.
    constructor.
    + eapply atom_to_semax_derives_pre;[|apply H]. Intros Q.
      Exists Q. apply andp_right. apply prop_right.
      inv H0. auto. solve_andp. 
    + eapply atom_to_semax_derives_pre_group;[|apply IHxs]. Intros Q.
      Exists Q. apply andp_right. apply prop_right.
      inv H0. auto. solve_andp.
Qed.


Lemma atom_return_to_semax_sem_group: forall xs R,
 Forall (atom_ret_to_semax Delta
  (EX Q : assert, !! Forall (atom_ret_to_semax Delta Q R) xs && Q) R) xs.
Proof.
  intros. induction xs;auto.
  - pose proof atom_return_to_semax_sem a R.
    constructor.
    + eapply atom_return_to_semax_derives_pre;[|apply H]. Intros Q.
      Exists Q. apply andp_right. apply prop_right.
      inv H0. auto. solve_andp. 
    + eapply atom_return_to_semax_derives_pre_group;[|apply IHxs]. Intros Q.
      Exists Q. apply andp_right. apply prop_right.
      inv H0. auto. solve_andp.
Qed.


(* Inversion Lemmas (part I) *)

(* Single Inversion Lemmas *)

Lemma post_conn_pre_to_semax_inv:
forall 
{s_pre} (c_pre: C_partial_pre s_pre)
{s_post} (c_post: C_partial_post s_post),
  path_to_semax Delta (Cpost_conn_Cpre c_post c_pre) ->
  post_to_semax Delta (EX R, R && !! pre_to_semax Delta R c_pre) c_post.
Proof.
  intros.
  induction c_post.
  { unfold Cpost_conn_Cpre in H.
    induction c_pre. simpl in H.
    apply path_to_statement_app in H.
    apply semax_seq_inv' in H.
    eapply post_to_semax_derives.
    2:{ apply H. }
    Intros Q. Exists Q.
    apply andp_right. solve_andp.
    apply prop_right. auto.
  }
  (* { intros a. apply H0. auto. } *)
Qed.


Lemma atom_conn_Cpre_nil: forall P s_pre (c_pre: C_partial_pre s_pre),
  pre_to_semax Delta P (atom_conn_Cpre (mk_atom []) c_pre) 
  <-> pre_to_semax Delta P c_pre.
Proof.
  intros. induction c_pre.
  - simpl. tauto.
Qed.

Lemma atom_conn_pre_to_semax_inv:
forall P atom {s_pre} (c_pre: C_partial_pre s_pre),
  pre_to_semax Delta P (atom_conn_Cpre atom c_pre) ->
  atom_to_semax Delta P (EX Q, Q && !! pre_to_semax Delta Q c_pre) atom.
Proof.
  intros P atom s_pre. destruct atom as [path]. 
  
  induction c_pre;intros.
  - simpl in H. apply path_to_statement_app in H.
    apply semax_seq_inv in H. destruct H as [Q [H1 H2]].
    eapply semax_conseq;[..|apply H1];try solve [intros; solve_andp].
    rewrite normal_split_assert_elim. Exists Q.
    apply andp_right;try solve_andp.
    apply prop_right;simpl;auto.
Qed.


Lemma post_conn_atom_to_semax_inv: forall Q s_post 
(c_post: C_partial_post s_post) atom,
post_to_semax Delta Q (Cpost_conn_atom c_post atom) ->
post_to_semax Delta
  (EX R, R && !! atom_to_semax Delta R Q atom) c_post.
Proof.
  intros.
  induction c_post.
  - destruct atom. simpl in H.
    apply path_to_statement_app in H.
    apply semax_seq_inv' in H.
    eapply semax_conseq;[..|apply H];try solve [intros; solve_andp].
    rewrite !normal_split_assert_elim.
    rewrite overridePost_normal_split.
    rewrite !normal_split_assert_elim.
    Intros Q0.
    Exists Q0. apply andp_right. solve_andp.
    apply prop_right. auto.
  (* - intros a. apply H0. simpl in H. destruct atom. *)
    (* apply H. *)
Qed.


Lemma atom_conn_return_to_semax_inv: forall s_atom1 s_atom2 P R,
(atom_ret_to_semax Delta P R) (atom_conn_return s_atom1 s_atom2) ->
(atom_to_semax Delta P 
  (EX Q, Q && !! (atom_ret_to_semax Delta Q R) s_atom2)) s_atom1.
Proof.
  intros.
  destruct s_atom2, s_atom1. unfold atom_to_semax.
  simpl in H.
  replace (p0 ++ p) with ((p0 ++ p) ++ nil) in H by apply app_nil_r.
  apply path_to_statement_app in H.
  apply semax_seq_inv in H. destruct H as [Qr [H H']].
  apply path_to_statement_app in H.
  apply semax_seq_inv' in H.

  eapply semax_noreturn_inv
  with (Post':=
    (normal_split_assert (EX Q0 : environ -> mpred,
    !! semax Delta Q0 (path_to_statement p Clight.Sskip)
        (overridePost Qr (return_split_assert R)) && Q0
    ))) in H;
  try solve [unfold_der; reflexivity].
  2:{ apply noreturn_split_result. auto. }
  
  eapply semax_conseq;[..|apply H];try solve [intros;solve_andp].
  { rewrite !normal_split_assert_elim.
    Intros Q. Exists Q. apply andp_right.
    solve_andp. apply prop_right.
    simpl. replace p with (p ++ nil) by apply app_nil_r.
    apply path_to_statement_app.
    eapply semax_seq. apply H0.
    apply H'. }
Qed.


Lemma post_conn_return_to_semax_inv: forall Q s_post 
(c_post: C_partial_post s_post) atom,
post_ret_to_semax Delta Q (Cpost_conn_return c_post atom) ->
post_to_semax Delta
  (EX R, R && !! atom_ret_to_semax Delta R Q atom) c_post.
Proof.
  intros.
  induction c_post.
  - destruct atom. simpl in H.
    replace (path ++ p) with ((path ++ p) ++ nil) in H by apply app_nil_r.
    apply path_to_statement_app in H.
    apply semax_seq_inv in H. destruct H as [Qr [H H']].
    apply path_to_statement_app in H.
    apply semax_seq_inv' in H. unfold post_to_semax.

    eapply semax_noreturn_inv
    with (Post':=
    (normal_split_assert ((EX Q0 : environ -> mpred,
    !! semax Delta Q0 (path_to_statement p Clight.Sskip)
         (overridePost Qr (return_split_assert Q)) && Q0
    ))))
    in H;
    try solve [unfold_der;reflexivity].
    2:{ apply noreturn_split_result. auto. }
    
    eapply semax_conseq;[..|apply H];try solve [intros;solve_andp].
    { rewrite !normal_split_assert_elim.
      Intros R. Exists R. apply andp_right.
      solve_andp. apply prop_right.
      simpl. replace p with (p ++ nil) by apply app_nil_r.
      apply path_to_statement_app.
      eapply semax_seq. apply H0.
      apply H'. }
Qed.


Lemma atom_conn_atom_to_semax_inv: forall s_atom1 s_atom2 P R,
(atom_to_semax Delta P R) (atom_conn_atom s_atom1 s_atom2) ->
(atom_to_semax Delta P 
  (EX Q, Q && !! (atom_to_semax Delta Q R) s_atom2)) s_atom1.
Proof.
  intros.
  destruct s_atom2, s_atom1. unfold atom_to_semax.
  simpl in H. apply path_to_statement_app in H.
  apply semax_seq_inv' in H.
  eapply semax_conseq;[..|apply H];try solve [intros; solve_andp].
  rewrite overridePost_normal_split. rewrite normal_split_assert_elim.
  Intros Q.
  Exists Q. apply andp_right. solve_andp.
  apply prop_right;auto.
Qed.

Lemma add_Q_to_Cposts_inv: forall P 
  s_post (c_post: C_partial_posts s_post),
CForall (@path_to_semax  CS Espec Delta) (add_Q_to_Cposts FF c_post) ->
CForall (@post_to_semax  CS Espec Delta P) c_post.
Proof.
  induction c_post;auto.
  intros. destruct H.
  apply IHc_post in H0. split;auto.
  clear H0 IHc_post.
  induction r'.
  - hnf. hnf in H.
    eapply semax_conseq;[..|apply H];try solve [intros; solve_andp].
    rewrite normal_split_assert_elim.
    eapply derives_trans;[|apply FF_left].
    solve_andp.
  (* - simpl. intros a. apply H0.
    simpl in H. destruct s. simpl in H.
    apply H. *)
Qed.

(* Rewriting Lemmas *)
Lemma atoms_conn_Cpres_distrib:
  forall P s_atoms s_pre c_pre s_pres' c_pres',
  CForall (@pre_to_semax CS Espec Delta P) 
      (atoms_conn_Cpres s_atoms
         (list_binded_cons s_pre c_pre s_pres' c_pres')) <->
  CForall (@pre_to_semax CS Espec Delta P) (atoms_conn_Cpres s_atoms { c_pre }) /\
  CForall (@pre_to_semax CS Espec Delta P) (atoms_conn_Cpres s_atoms c_pres').
Proof.
  intros. induction s_atoms.
  - simpl. tauto.
  - split;intro.
    + simpl in H. inversion H.
      destruct_CForalls H1.
      apply IHs_atoms in H1_0. destruct H1_0.
      simpl. split.
      * constructor;auto.
      * apply CForall_Capp;auto.
    + destruct H. inversion H.
      simpl in H0. apply CForall_Capp in H0.
      destruct H0.
      simpl. constructor;auto.
      apply CForall_Capp. split;auto.
      apply IHs_atoms. auto.
Qed.

Lemma Cpost_atom_conn_distrib: forall a s_posts (c_posts: C_partial_posts s_posts),
(Cmap (fun s_post1 : S_partial_post => Spost_conn_atom s_post1 a)
    (fun (s_post1 : S_partial_post) (c_post1 : C_partial_post s_post1) =>
    Cpost_conn_atom c_post1 a) c_posts) = (Cposts_conn_atom c_posts a).
Proof.
  intros. induction c_posts.
  - simpl. tauto.
  - split;intro.
Qed.

Lemma Cpost_return_conn_distrib: forall a s_posts (c_posts: C_partial_posts s_posts),
(Cmap (fun s_post1 : S_partial_post => Spost_conn_return s_post1 a)
    (fun (s_post1 : S_partial_post) (c_post1 : C_partial_post s_post1) =>
    Cpost_conn_return c_post1 a) c_posts) = (Cposts_conn_return c_posts a).
Proof.
  intros. induction c_posts.
  - simpl. tauto.
  - split;intro.
Qed.

Lemma Cposts_atoms_conn_distrib:
  forall P s_atoms s_post c_post s_posts' c_posts',
  CForall (@post_to_semax CS Espec Delta P) 
      (Cposts_conn_atoms 
         (list_binded_cons s_post c_post s_posts' c_posts')
         s_atoms) <->
  CForall (@post_to_semax CS Espec Delta P) (Cposts_conn_atoms { c_post } s_atoms ) /\
  CForall (@post_to_semax CS Espec Delta P) (Cposts_conn_atoms c_posts' s_atoms).
Proof.
  intros. induction s_atoms.
  - simpl. tauto.
  - split;intro.
    + simpl in H. inversion H.
      destruct_CForalls H1.
      apply IHs_atoms in H1_0. destruct H1_0.
      simpl. split.
      * constructor;auto.
      * apply CForall_Capp. split;auto.
        (* clear H H1 H2 IHs_atoms.
        induction c_posts'.
        { constructor. }
        { destruct H1_. apply IHc_posts' in H1.
          constructor;auto.
          rewrite Cpost_atom_conn_distrib. auto. } *)
    + destruct H. destruct H. simpl in H1.
      simpl in H0. destruct_CForalls H0.
      constructor;auto.
      apply CForall_Capp. split;auto.
      (* { rewrite Cpost_atom_conn_distrib. auto. } *)
      { apply IHs_atoms. auto. }
Qed.

Lemma Cposts_returns_conn_distrib:
  forall P s_atoms s_post c_post s_posts' c_posts',
  CForall (@post_ret_to_semax CS Espec Delta P) 
      (Cposts_conn_returns 
         (list_binded_cons s_post c_post s_posts' c_posts')
         s_atoms) <->
  CForall (@post_ret_to_semax CS Espec Delta P) (Cposts_conn_returns { c_post }s_atoms ) /\
  CForall (@post_ret_to_semax CS Espec Delta P) (Cposts_conn_returns c_posts' s_atoms).
Proof.
  intros. induction s_atoms.
  - simpl. tauto.
  - split;intro.
    + simpl in H. inversion H.
      destruct_CForalls H1.
      apply IHs_atoms in H1_0. destruct H1_0.
      simpl. split.
      * constructor;auto.
      * apply CForall_Capp. split;auto.
        (* clear H H1 H2 IHs_atoms.
        induction c_posts'.
        { constructor. }
        { destruct H1_. apply IHc_posts' in H1.
          constructor;auto.
          rewrite Cpost_return_conn_distrib. auto. } *)
    + destruct H. destruct H. simpl in H1.
      simpl in H0. destruct_CForalls H0.
      constructor;auto.
      apply CForall_Capp. split;auto.
      (* { rewrite Cpost_return_conn_distrib. auto. } *)
      { apply IHs_atoms. auto. }
Qed.

Lemma atoms_conn_nil_returns: forall atoms,
  atoms_conn_returns atoms [] = [].
Proof.
  induction atoms;auto.
Qed.

Lemma atoms_conn_nil_atoms: forall atoms,
  atoms_conn_atoms atoms [] = [].
Proof.
  induction atoms;auto.
Qed.

Lemma nil_atoms_conn_atoms: forall atoms,
  atoms_conn_atoms [] atoms = [].
Proof.
  induction atoms;auto.
Qed.


Lemma nil_atoms_conn_returns: forall atoms,
  atoms_conn_returns [] atoms = [].
Proof.
  induction atoms;auto.
Qed.

Lemma nil_atoms_conn_Cpres: forall spres (cpres: C_partial_pres spres) ,
  atoms_conn_Cpres [] cpres = {}.
Proof.
  induction cpres;auto.
Qed.


Lemma atoms_conn_nil_Spres_sem: forall Q atoms,
CForall (@pre_to_semax CS Espec Delta Q) (atoms_conn_Cpres atoms {}).
Proof.
  induction atoms;auto.
  simpl. tauto.
Qed.



Lemma Cposts_returns_conn_app_distrib:
  forall P s_atoms s_post1 
    (c_post1: C_partial_posts s_post1) s_post2 
    (c_post2: C_partial_posts s_post2),
  CForall (@post_ret_to_semax CS Espec Delta P) 
      (Cposts_conn_returns 
         (c_post1 +++ c_post2)
         s_atoms) <->
  CForall (@post_ret_to_semax CS Espec Delta P) (Cposts_conn_returns c_post1 s_atoms ) /\
  CForall (@post_ret_to_semax CS Espec Delta P) (Cposts_conn_returns c_post2 s_atoms).
Proof.
  intros.
  induction c_post1.
  - simpl. split;intro;try(split;auto).
    + clear H. induction s_atoms;auto.
    constructor.
    + destruct H;auto.
  - split;intro.
    + simpl in H.
      apply Cposts_returns_conn_distrib in H.
      destruct H. apply IHc_post1 in H0.
      destruct H0. split;auto.
      apply Cposts_returns_conn_distrib. split;auto.
    + destruct H. simpl. apply Cposts_returns_conn_distrib.
      apply Cposts_returns_conn_distrib in H.
      destruct H.
      split;auto. apply IHc_post1. split;auto.
Qed.


Lemma Cposts_atoms_conn_app_distrib:
  forall P s_atoms s_post1 
    (c_post1: C_partial_posts s_post1) s_post2 
    (c_post2: C_partial_posts s_post2),
  CForall (@post_to_semax CS Espec Delta P) 
      (Cposts_conn_atoms (c_post1 +++ c_post2) s_atoms) <->
  CForall (@post_to_semax  CS Espec Delta P) (Cposts_conn_atoms c_post1 s_atoms ) /\
  CForall (@post_to_semax CS Espec Delta  P) (Cposts_conn_atoms c_post2 s_atoms).
Proof.
  intros.
  induction c_post1.
  - simpl. split;intro;try(split;auto).
    + clear H. induction s_atoms;auto.
    constructor.
    + destruct H;auto.
  - split;intro.
    + simpl in H.
      apply Cposts_atoms_conn_distrib in H.
      destruct H. apply IHc_post1 in H0.
      destruct H0. split;auto.
      apply Cposts_atoms_conn_distrib. split;auto.
    + destruct H. simpl. apply Cposts_atoms_conn_distrib.
      apply Cposts_atoms_conn_distrib in H.
      destruct H.
      split;auto. apply IHc_post1. split;auto.
Qed.

Lemma Cposts_atoms_conn_app_distrib2:
  forall P s_atoms1 s_atoms2 s_post
    (c_post: C_partial_posts s_post),
  CForall (@post_to_semax CS Espec Delta P) 
      (Cposts_conn_atoms c_post (s_atoms1 ++ s_atoms2)) <->
  CForall (@post_to_semax CS Espec Delta P) (Cposts_conn_atoms c_post s_atoms1) /\
  CForall (@post_to_semax  CS Espec Delta P) (Cposts_conn_atoms c_post s_atoms2).
Proof.
  intros.
  induction s_atoms1.
  - split;intro.
    + simpl in H. simpl. auto.
    + simpl in *.
      destruct H. auto.
  - split;intro.
    + simpl in H.
      apply CForall_Capp in H.
      destruct H. apply IHs_atoms1 in H0.
      destruct H0. split;auto.
      simpl. apply CForall_Capp. auto.
    + simpl. apply CForall_Capp. auto.
      destruct H. simpl in H. apply CForall_Capp in H.
      destruct H. split;auto. apply IHs_atoms1. auto.
Qed.


Lemma Cposts_returns_conn_app_distrib2:
  forall P s_atoms1 s_atoms2 s_post
    (c_post: C_partial_posts s_post),
  CForall (@post_ret_to_semax  CS Espec Delta P) 
      (Cposts_conn_returns c_post (s_atoms1 ++ s_atoms2)) <->
  CForall (@post_ret_to_semax  CS Espec Delta P) (Cposts_conn_returns c_post s_atoms1) /\
  CForall (@post_ret_to_semax  CS Espec Delta P) (Cposts_conn_returns c_post s_atoms2).
Proof.
  intros.
  induction s_atoms1.
  - split;intro.
    + simpl in H. simpl. auto.
    + simpl in *.
      destruct H. auto.
  - split;intro.
    + simpl in H.
      apply CForall_Capp in H.
      destruct H. apply IHs_atoms1 in H0.
      destruct H0. split;auto.
      simpl. apply CForall_Capp. auto.
    + simpl. apply CForall_Capp. auto.
      destruct H. simpl in H. apply CForall_Capp in H.
      destruct H. split;auto. apply IHs_atoms1. auto.
Qed.

Lemma post_conn_atom_conn_return_assoc: forall Q s_post1
  (post1 :C_partial_post s_post1) atom2 atom1,
post_ret_to_semax Delta Q (Cpost_conn_return post1 (atom_conn_return atom1 atom2)) <->
post_ret_to_semax Delta Q (Cpost_conn_return (Cpost_conn_atom post1 atom1) atom2).
Proof.
  intros. destruct atom2, atom1. induction post1.
  + simpl. rewrite app_assoc. tauto.
  (* + simpl. split;intro.
    * intros a. apply H. auto.
    * intros a. apply H. auto. *)
Qed.

Lemma post_conn_atom_conn_atom_assoc: forall Q s_post1
  (post1 :C_partial_post s_post1) atom2 atom1,
post_to_semax Delta Q (Cpost_conn_atom post1 (atom_conn_atom atom1 atom2)) <->
post_to_semax Delta Q (Cpost_conn_atom (Cpost_conn_atom post1 atom1) atom2).
Proof.
  intros. destruct atom2, atom1. induction post1.
  + simpl. rewrite app_assoc. tauto.
  (* + simpl. split;intro.
    * intros a. apply H. auto.
    * intros a. apply H. auto. *)
Qed.


Lemma posts_conn_atom_conn_returns_assoc: forall Q s_post1
  (post1 :C_partial_posts s_post1) atom2 atom1,
CForall (@post_ret_to_semax CS Espec Delta Q)
(Cposts_conn_returns post1 (atom_conn_returns atom2 atom1)) <->
CForall (@post_ret_to_semax CS Espec Delta Q)
  (Cposts_conn_returns (Cposts_conn_atom post1 atom2) atom1).
Proof.
  intros.
  induction atom1;simpl.
  - tauto.
  - split;intro.
    + apply CForall_Capp. apply CForall_Capp in H.
      destruct H. split;auto.
      2:{ apply IHatom1. auto. }
      clear H0. clear IHatom1.
      induction post1;auto.
      destruct H. rewrite Cpost_return_conn_distrib in H0.
      apply IHpost1 in H0. split;auto.
      (* 2:{ rewrite Cpost_return_conn_distrib.
          rewrite Cpost_atom_conn_distrib. auto. } *)
      apply post_conn_atom_conn_return_assoc. auto.
    + apply CForall_Capp. apply CForall_Capp in H.
      destruct H. split;auto.
      2:{ apply IHatom1. auto. }
      clear H0. clear IHatom1.
      induction post1;auto.
      destruct H. rewrite Cpost_return_conn_distrib in H0.
      rewrite Cpost_atom_conn_distrib in H0.
      apply IHpost1 in H0. split;auto.
      (* 2:{ rewrite Cpost_return_conn_distrib. auto. } *)
      apply post_conn_atom_conn_return_assoc. auto.
Qed.

Lemma posts_conn_atom_conn_atoms_assoc: forall Q s_post1
  (post1 :C_partial_posts s_post1) atom2 atom1,
CForall (@post_to_semax CS Espec Delta Q)
(Cposts_conn_atoms post1 (atom_conn_atoms atom2 atom1)) <->
CForall (@post_to_semax  CS Espec Delta Q)
  (Cposts_conn_atoms (Cposts_conn_atom post1 atom2) atom1).
Proof.
  intros.
  induction atom1;simpl.
  - tauto.
  - split;intro.
    + apply CForall_Capp. apply CForall_Capp in H.
      destruct H. split;auto.
      2:{ apply IHatom1. auto. }
      clear H0. clear IHatom1.
      induction post1;auto.
      destruct H. rewrite Cpost_atom_conn_distrib in H0.
      apply IHpost1 in H0. split;auto.
      (* 2:{ rewrite Cpost_atom_conn_distrib.
          rewrite Cpost_atom_conn_distrib. auto. } *)
      apply post_conn_atom_conn_atom_assoc. auto.
    + apply CForall_Capp. apply CForall_Capp in H.
      destruct H. split;auto.
      2:{ apply IHatom1. auto. }
      clear H0. clear IHatom1.
      induction post1;auto.
      destruct H. rewrite Cpost_atom_conn_distrib in H0.
      rewrite Cpost_atom_conn_distrib in H0.
      apply IHpost1 in H0. split;auto.
      (* 2:{ rewrite Cpost_atom_conn_distrib. auto. } *)
      apply post_conn_atom_conn_atom_assoc. auto.
Qed.

(* Rewriting distr semax rules *)
Lemma posts_conn_atoms_conn_returns_assoc: forall Q s_post1
  (post1 :C_partial_posts s_post1) atom2 atom1,
CForall (@post_ret_to_semax  CS Espec Delta Q)
(Cposts_conn_returns post1 (atoms_conn_returns atom2 atom1)) <->
CForall (@post_ret_to_semax  CS Espec Delta Q)
  (Cposts_conn_returns (Cposts_conn_atoms post1 atom2) atom1).
Proof.
  intros.
  induction atom2.
  - simpl. split;auto. intros.
    induction atom1;auto.
  - simpl; split;intro.
    + unfold atoms_conn_returns in H. simpl in H.
      apply Cposts_returns_conn_app_distrib.
      apply Cposts_returns_conn_app_distrib2 in H.
      destruct H. split;auto.
      2:{ apply IHatom2. auto. }
      apply posts_conn_atom_conn_returns_assoc. auto.
    + apply Cposts_returns_conn_app_distrib in H.
      destruct H. apply IHatom2 in H0.
      unfold atoms_conn_returns. simpl.
      apply Cposts_returns_conn_app_distrib2.
      split;auto.
      apply posts_conn_atom_conn_returns_assoc. auto.
Qed.

Lemma posts_conn_atoms_conn_atoms_assoc: forall Q s_post1
  (post1 :C_partial_posts s_post1) atom2 atom1,
CForall (@post_to_semax CS Espec Delta Q)
(Cposts_conn_atoms post1 (atoms_conn_atoms atom2 atom1)) <->
CForall (@post_to_semax CS Espec Delta Q)
  (Cposts_conn_atoms (Cposts_conn_atoms post1 atom2) atom1).
Proof.
  intros.
  induction atom2.
  - simpl. split;auto. intros.
    induction atom1;auto.
  - simpl; split;intro.
    + unfold atoms_conn_atoms in H. simpl in H.
      apply Cposts_atoms_conn_app_distrib.
      apply Cposts_atoms_conn_app_distrib2 in H.
      destruct H. split;auto.
      2:{ apply IHatom2. auto. }
      apply posts_conn_atom_conn_atoms_assoc. auto.
    + apply Cposts_atoms_conn_app_distrib in H.
      destruct H. apply IHatom2 in H0.
      unfold atoms_conn_atoms. simpl.
      apply Cposts_atoms_conn_app_distrib2.
      split;auto.
      apply posts_conn_atom_conn_atoms_assoc. auto.
Qed.


Lemma Cposts_Cpres_conn_distrib:
  forall s_posts (c_posts: C_partial_posts s_posts)
    s_pre (c_pre: C_partial_pre s_pre)
    s_pres' (c_pres': C_partial_pres s_pres'),
  CForall (@path_to_semax CS Espec Delta) 
      (Cposts_conn_Cpres c_posts 
         (list_binded_cons s_pre c_pre s_pres' c_pres')) <->
  CForall (@path_to_semax  CS Espec Delta)  (Cposts_conn_Cpres c_posts { c_pre } ) /\
  CForall (@path_to_semax  CS Espec Delta)  (Cposts_conn_Cpres c_posts c_pres').
Proof.
  intros. induction c_posts.
  - simpl. tauto.
  - split;intro.
    + simpl in H. inversion H.
      destruct_CForalls H1.
      apply IHc_posts in H1_0. destruct H1_0.
      simpl. split.
      * constructor;auto.
      * apply CForall_Capp. split;auto.
    + destruct H. destruct H. simpl in H1.
      simpl in H0. destruct_CForalls H0.
      constructor;auto.
      apply CForall_Capp. split;auto.
      { apply IHc_posts. auto. }
Qed.


Lemma Cposts_Cpres_conn_app_distrib1:
  forall s_pres (c_pres: C_partial_pres s_pres) 
    s_post1 (c_post1: C_partial_posts s_post1)
    s_post2 (c_post2: C_partial_posts s_post2), 
  CForall (@path_to_semax CS Espec Delta) 
      (Cposts_conn_Cpres (c_post1 +++ c_post2) c_pres) <->
  CForall (@path_to_semax CS Espec Delta) (Cposts_conn_Cpres c_post1 c_pres) /\
  CForall (@path_to_semax CS Espec Delta) (Cposts_conn_Cpres c_post2 c_pres).
Proof.
  intros.
  induction c_post1.
  - split;intro.
    + simpl in H. simpl. split; auto.
    + simpl in *.
      destruct H. auto.
  - split;intro.
    + simpl in H. apply CForall_Capp in H.
      destruct H. apply IHc_post1 in H0.
      destruct H0. split;auto. simpl.
      apply CForall_Capp. auto.
    + simpl. destruct H. simpl in H. apply CForall_Capp in H.
      destruct H. apply CForall_Capp. split;auto.
      apply IHc_post1. auto.
Qed.

Lemma Cposts_Cpres_conn_app_distrib2:
  forall s_pres1 (c_pres1: C_partial_pres s_pres1) 
    s_pres2 (c_pres2: C_partial_pres s_pres2) s_post
    (c_post: C_partial_posts s_post),
  CForall (@path_to_semax CS Espec Delta) 
      (Cposts_conn_Cpres c_post (c_pres1 +++ c_pres2)) <->
  CForall (@path_to_semax CS Espec Delta) (Cposts_conn_Cpres c_post c_pres1) /\
  CForall (@path_to_semax CS Espec Delta) (Cposts_conn_Cpres c_post c_pres2).
Proof.
  intros.
  induction c_pres1.
  - split;intro.
    + simpl in H. simpl. split; auto.
      clear H.
      induction c_post;auto. constructor.
    + simpl in *.
      destruct H. auto.
  - split;intro.
    + simpl in H. apply Cposts_Cpres_conn_distrib in H.
      destruct H. apply IHc_pres1 in H0.
      destruct H0. split;auto.
      apply Cposts_Cpres_conn_distrib.
      split;auto.
    + simpl. apply Cposts_Cpres_conn_distrib. destruct H.
      apply Cposts_Cpres_conn_distrib in H. destruct H.
      split;auto. apply IHc_pres1. auto.
Qed.


Lemma post_conn_atom_conn_pre_assoc: forall 
  s_post (post1: C_partial_post s_post)  
  atom2 s_pre (pre1: C_partial_pre s_pre),
path_to_semax Delta
(Cpost_conn_Cpre (Cpost_conn_atom post1 atom2) pre1) <->
path_to_semax Delta
(Cpost_conn_Cpre post1 (atom_conn_Cpre atom2 pre1)).
Proof.
  intros. destruct atom2. 
  destruct pre1.
  induction post1.
  - simpl. rewrite app_assoc. tauto.
  (* - split;intros.
    + intros a. apply H. auto.
    + intros a. apply H. auto. *)
Qed.    


Lemma post_conn_atom_conn_pres_assoc: forall 
  s_post (post1: C_partial_post s_post)  
  atom2 s_pre (pre1: C_partial_pres s_pre),
CForall (@path_to_semax CS Espec Delta)
(Cpost_conn_Cpres (Cpost_conn_atom post1 atom2) pre1) <->
CForall (@path_to_semax CS Espec Delta)
(Cpost_conn_Cpres post1 (atom_conn_Cpres atom2 pre1)).
Proof.
  intros.
  induction pre1.
  - simpl. split;auto.
  - split;intros.
    + destruct H. apply IHpre1 in H0.
      split;auto. apply post_conn_atom_conn_pre_assoc. auto.
    + destruct H. apply IHpre1 in H0.
      split;auto. apply post_conn_atom_conn_pre_assoc. auto.
Qed.

Lemma posts_conn_atom_conn_pres_assoc: forall 
  s_post (post1: C_partial_posts s_post)  
  atom2 s_pre (pre1: C_partial_pres s_pre),
CForall (@path_to_semax CS Espec Delta)
(Cposts_conn_Cpres (Cposts_conn_atom post1 atom2) pre1) <->
CForall (@path_to_semax CS Espec Delta)
(Cposts_conn_Cpres post1 (atom_conn_Cpres atom2 pre1)).
Proof.
  intros.
  induction post1;simpl.
  - split;intro;auto.
  - split;intro.
    + apply CForall_Capp. apply CForall_Capp in H. destruct H.
      rewrite Cpost_atom_conn_distrib in H0.
      apply IHpost1 in H0. split;auto.
      apply post_conn_atom_conn_pres_assoc. auto.
    + apply CForall_Capp. apply CForall_Capp in H. destruct H.
      rewrite Cpost_atom_conn_distrib. 
      apply IHpost1 in H0. split;auto.
      apply post_conn_atom_conn_pres_assoc. auto.
Qed.


Lemma posts_conn_atoms_conn_pres_assoc: forall 
  s_post (post1: C_partial_posts s_post)  
  atom2 s_pre (pre1: C_partial_pres s_pre),
CForall (@path_to_semax CS Espec Delta)
(Cposts_conn_Cpres (Cposts_conn_atoms post1 atom2) pre1) <->
CForall (@path_to_semax CS Espec Delta)
(Cposts_conn_Cpres post1 (atoms_conn_Cpres atom2 pre1)).
Proof.
  intros. induction atom2.
  - simpl. split;auto. intros.
    induction post1; auto.
  - split;intro.
    + simpl in H. apply Cposts_Cpres_conn_app_distrib1 in H.
      destruct H. apply IHatom2 in H0. simpl.
      apply Cposts_Cpres_conn_app_distrib2.
      split;auto.
      apply posts_conn_atom_conn_pres_assoc. auto.
    + simpl in H. apply Cposts_Cpres_conn_app_distrib2 in H.
      destruct H. apply IHatom2 in H0. simpl.
      apply Cposts_Cpres_conn_app_distrib1. split;auto.
      apply posts_conn_atom_conn_pres_assoc. auto.
Qed.


(* Single-Grouped Inversion Lemmas *)
Lemma atoms_conn_pre_to_semax_inv: forall P s_atoms s_pre
  (c_pre: C_partial_pre s_pre),
CForall (@pre_to_semax  CS Espec Delta P) (atoms_conn_Cpres s_atoms {c_pre})
-> Forall (atom_to_semax Delta P
   (EX Q, Q &&
    !! CForall (@pre_to_semax  CS Espec Delta Q) { c_pre })) s_atoms.
Proof.
  intros.
  induction s_atoms.
  - auto.
  - simpl in H. inversion H.
    apply IHs_atoms in H1.
    apply atom_conn_pre_to_semax_inv in H0.
    constructor;auto.
    eapply atom_to_semax_derives_post;[|apply H0].
    Intros Q. Exists Q.
    apply andp_right;try solve_andp.
    apply prop_right. constructor;auto.
    constructor.
Qed.


Lemma post_conn_pres_group_inv: forall s_post 
(c_post: C_partial_post s_post) s_pres
(c_pres: C_partial_pres s_pres),
CForall (@path_to_semax CS Espec Delta) 
        (Cpost_conn_Cpres c_post c_pres) ->
s_pres = [] \/
(@post_to_semax   CS Espec Delta
  (EX Q, Q && !! 
      CForall (@pre_to_semax CS Espec Delta  Q) c_pres) _ c_post).
Proof.
  intros.
  induction c_pres.
  - auto.
  - right. destruct H.
    apply IHc_pres in H0. clear IHc_pres.
    destruct H0.
    { subst l. rewrite (lb_nil_inv c_pres).
      apply post_conn_pre_to_semax_inv in H.
      eapply post_to_semax_derives;[|apply H].
      Intros R. Exists R. apply andp_right.
      solve_andp. apply prop_right.
      constructor;auto. constructor. }
    { apply post_conn_pre_to_semax_inv in H.
      eapply post_to_semax_derives;
        [..|apply post_to_semax_conj_rule;[apply H|apply H0]].
      Intros Q1 Q2. Exists (Q1 && Q2).
      apply andp_right. solve_andp. apply prop_right.
      constructor;auto.
      { eapply pre_to_semax_derives;[..|apply H1].
        solve_andp.
      }
      { eapply CForall_impl;[|apply H2].
        intros. eapply pre_to_semax_derives;[..|apply H3].
        solve_andp.
      }
    }
Qed.


Lemma posts_conn_atom_group_inv: forall s_posts
  (c_posts: C_partial_posts s_posts) atom Q,
CForall (@post_to_semax  CS Espec Delta Q)
        (Cposts_conn_atom c_posts atom) ->
CForall (@post_to_semax   CS Espec Delta
  (EX R, R && !! atom_to_semax Delta R Q atom)) c_posts.
Proof.
  intros.
  induction c_posts;auto.
  destruct H.
  rewrite Cpost_atom_conn_distrib in H0.
  specialize (IHc_posts H0).
  constructor;auto.
  apply post_conn_atom_to_semax_inv. auto.
Qed.
  

Lemma atom_conn_returns_to_semax_inv: forall s_atom1 s_atoms2 P R,
Forall (atom_ret_to_semax Delta P R) (atom_conn_returns s_atom1 s_atoms2) ->
s_atoms2 = [] \/
(atom_to_semax Delta P 
  (EX Q, Q && !! Forall (atom_ret_to_semax Delta Q R) s_atoms2)) s_atom1.
Proof.
  intros.
  induction s_atoms2.
  - auto.
  - simpl in H. inversion H;subst.
    specialize (IHs_atoms2 H3). destruct IHs_atoms2.
    { subst. right.
      apply atom_conn_return_to_semax_inv in H2.
      eapply atom_to_semax_derives_post;[|apply H2].
      Intros Q.
      Exists Q. apply andp_right. solve_andp.
      apply prop_right. constructor;auto.
    }
    { subst. right.
      apply atom_conn_return_to_semax_inv in H2.
      pose proof atom_to_semax_conj_rule _ _ _ _ H0 H2.
      eapply atom_to_semax_derives_post;[|apply H1].
      Intros Q1 Q2. Exists (Q1 && Q2).
      apply andp_right. solve_andp. apply prop_right. constructor.
      { eapply atom_return_to_semax_derives_pre;[|apply H5]. solve_andp. }
      { eapply Forall_impl;[|apply H4]. intros.
        eapply atom_return_to_semax_derives_pre;[|apply H6]. solve_andp. }
    }
Qed.


Lemma atom_conn_atoms_to_semax_inv: forall s_atom1 s_atoms2 P R,
Forall (atom_to_semax Delta P R) (atom_conn_atoms s_atom1 s_atoms2) ->
s_atoms2 = [] \/
(atom_to_semax Delta P 
  (EX Q, Q && !! Forall (atom_to_semax Delta Q R) s_atoms2)) s_atom1.
Proof.
  intros.
  induction s_atoms2.
  - auto.
  - simpl in H. inversion H;subst.
    specialize (IHs_atoms2 H3). destruct IHs_atoms2.
    { subst. right.
      apply atom_conn_atom_to_semax_inv in H2.
      eapply atom_to_semax_derives_post;[|apply H2].
      Intros Q.
      Exists Q. apply andp_right. solve_andp.
      apply prop_right. constructor;auto.
    }
    { subst. right.
      apply atom_conn_atom_to_semax_inv in H2.
      pose proof atom_to_semax_conj_rule  _ _ _ _ H0 H2.
      eapply atom_to_semax_derives_post;[|apply H1].
      Intros Q1 Q2. Exists (Q1 && Q2).
      apply andp_right. solve_andp. apply prop_right. constructor.
      { eapply atom_to_semax_derives_pre;[|apply H5]. solve_andp. }
      { eapply Forall_impl;[|apply H4]. intros.
        eapply atom_to_semax_derives_pre;[|apply H6]. solve_andp. }
    }
Qed.


Lemma posts_conn_return_group_inv: forall s_posts
  (c_posts: C_partial_posts s_posts) atom Q,
CForall (@post_ret_to_semax   CS Espec Delta Q)
        (Cposts_conn_return c_posts atom) ->
CForall (@post_to_semax   CS Espec Delta
  (EX R, R && !! atom_ret_to_semax Delta R Q atom)) c_posts.
Proof.
  intros.
  induction c_posts;auto.
  destruct H.
  rewrite Cpost_return_conn_distrib in H0.
  specialize (IHc_posts H0).
  constructor;auto.
  apply post_conn_return_to_semax_inv. auto.
Qed.

(* Grouped Inversion lemmas *)

Lemma atoms_conn_pres_group_inv: forall P s_atoms 
  s_pres {c_pres: C_partial_pres s_pres},
CForall (@pre_to_semax  CS Espec Delta P)
  (atoms_conn_Cpres s_atoms c_pres) ->
(s_pres = []) \/
Forall (@atom_to_semax  CS Espec Delta P
  (EX Q, Q && !! CForall (@pre_to_semax  CS Espec Delta Q) c_pres))
  s_atoms.
Proof with auto.
  intros P s_atoms s_pres.
  induction s_pres as [|s_pre s_pres'];intros.
  - left;auto.
  - right. destruct (lb_cons_inv c_pres) as [c_pre [c_pres' E]]. subst.
    apply atoms_conn_Cpres_distrib in H. destruct H.
    apply IHs_pres' in H0. destruct H0;auto.
    { subst s_pres'. rewrite (lb_nil_inv c_pres').
      apply atoms_conn_pre_to_semax_inv in H. auto. }
    { apply atoms_conn_pre_to_semax_inv in H.
      apply Forall_forall. intros.
      apply Forall_forall with (x:=x) in H;auto.
      apply Forall_forall with (x:=x) in H0;auto.
      eapply atom_to_semax_derives_post;
        [..|apply atom_to_semax_conj_rule;[apply H|apply H0]].
        Intros Q1 Q2. Exists (Q1 && Q2).
        apply andp_right. solve_andp. apply prop_right.
      constructor;auto.
      { inversion H2.
        eapply pre_to_semax_derives;[..|apply H4].
        solve_andp.
      }
      { eapply CForall_impl;[|apply H3].
        intros. eapply pre_to_semax_derives;[..|apply H4].
        solve_andp.
      }
    }
Qed.

Lemma posts_conn_pres_group_inv: forall s_posts
  (c_posts: C_partial_posts s_posts) s_pres
  (c_pres: C_partial_pres s_pres),
CForall (@path_to_semax CS Espec Delta ) (Cposts_conn_Cpres c_posts c_pres) ->
s_pres = [] \/
CForall (@post_to_semax   CS Espec Delta
  (EX Q, Q && !! CForall (@pre_to_semax  CS Espec Delta Q) c_pres))
 c_posts.
Proof.
  intros. induction c_posts.
  - right. constructor.
  - simpl in H. destruct_CForalls H.
    apply IHc_posts in H_0. destruct H_0;auto.
    clear IHc_posts.
    apply post_conn_pres_group_inv in H_.
    destruct H_;auto. right.
    constructor;auto.
Qed.


Lemma posts_conn_atoms_group_inv: forall s_posts
  (c_posts: C_partial_posts s_posts) atoms Q,
CForall (@post_to_semax  CS Espec Delta Q)
        (Cposts_conn_atoms c_posts atoms) ->
atoms = [] \/
CForall (@post_to_semax   CS Espec Delta 
  (EX R, R && !! Forall (atom_to_semax  Delta R Q) atoms)) c_posts.
Proof.
  intros. induction atoms.
  - auto.
  - right. simpl in H.
    destruct_CForalls H.
    specialize (IHatoms H_0).
    destruct IHatoms.
    { subst. apply posts_conn_atom_group_inv in H_.
      eapply CForall_impl;[|apply H_].
      intros. eapply post_to_semax_derives;[..|apply H].
      Intros R. Exists R. apply andp_right.
      solve_andp. apply prop_right.
      constructor;auto.
    }
    { apply posts_conn_atom_group_inv in H_.
      eapply CForall_impl with (P:=
      (@post_to_semax CS Espec Delta 
        ((EX R1, R1 && !! (atom_to_semax Delta  R1 Q a))
        && EX R2, R2 && !! Forall (atom_to_semax Delta  R2 Q) atoms))).
      { intros. eapply post_to_semax_derives;[..|apply H0].
      Intros Q1 Q2. Exists (Q1 && Q2).
      apply andp_right. solve_andp. apply prop_right. constructor.
        { eapply atom_to_semax_derives_pre;[|apply H1]. solve_andp. }
        { eapply Forall_impl;[|apply H2].
          intros. eapply atom_to_semax_derives_pre;[|apply H3].
          solve_andp. }
      }
      pose proof CForall_conj _ _ _ H_ H.
      eapply CForall_impl;[|apply H0].
      intros.
      simpl in H1. destruct H1. apply post_to_semax_conj_rule;auto.
    }
Qed.




Lemma posts_conn_returns_group_inv: forall s_posts
  (c_posts: C_partial_posts s_posts) atoms Q,
CForall (@post_ret_to_semax  CS Espec Delta Q)
        (Cposts_conn_returns c_posts atoms) ->
atoms = [] \/
CForall (@post_to_semax   CS Espec Delta
  (EX R, R && !! Forall (atom_ret_to_semax Delta  R Q) atoms)) c_posts.
Proof.
  intros. induction atoms.
  - auto.
  - right. simpl in H.
    destruct_CForalls H.
    specialize (IHatoms H_0).
    destruct IHatoms.
    { subst. apply posts_conn_return_group_inv in H_.
      eapply CForall_impl;[|apply H_].
      intros. eapply post_to_semax_derives;[..|apply H].
      Intros R. Exists R. apply andp_right.
      solve_andp. apply prop_right.
      constructor;auto.
    }
    { apply posts_conn_return_group_inv in H_.
      eapply CForall_impl with (P:=
      (@post_to_semax CS Espec Delta
        ((EX R1, R1 && !! (atom_ret_to_semax  Delta R1 Q a))
        && EX R2, R2 && !! Forall (atom_ret_to_semax  Delta R2 Q) atoms))).
      { intros. eapply post_to_semax_derives;[..|apply H0].
      Intros Q1 Q2. Exists (Q1 && Q2).
      apply andp_right. solve_andp. apply prop_right. constructor.
        { eapply atom_return_to_semax_derives_pre;[|apply H1]. solve_andp. }
        { eapply Forall_impl;[|apply H2].
          intros. eapply atom_return_to_semax_derives_pre;[|apply H3].
          solve_andp. }
      }
      pose proof CForall_conj _ _ _ H_ H.
      eapply CForall_impl;[|apply H0].
      intros.
      simpl in H1. destruct H1. apply post_to_semax_conj_rule;auto.
    }
Qed.


Lemma atoms_conn_atoms_group_inv: forall s_atoms1 s_atoms2 P R,
Forall (atom_to_semax Delta  P R) (atoms_conn_atoms s_atoms1 s_atoms2) ->
s_atoms2 = [] \/
Forall (atom_to_semax Delta  P 
  (EX Q, Q && !! Forall (atom_to_semax  Delta Q R) s_atoms2)) s_atoms1.
Proof.
  intros. induction s_atoms1.
  - right. constructor.
  - unfold atoms_conn_atoms in H.
    simpl in H. apply Forall_app in H. destruct H.
    specialize (IHs_atoms1 H0).
    destruct IHs_atoms1;auto.
    apply atom_conn_atoms_to_semax_inv in H.
    destruct H;auto.
Qed.



Lemma atoms_conn_returns_group_inv: forall s_atoms1 s_atoms2 P R,
Forall (atom_ret_to_semax  Delta P R) (atoms_conn_returns s_atoms1 s_atoms2) ->
s_atoms2 = [] \/
Forall (atom_to_semax  Delta P 
  (EX Q, Q && !! Forall (atom_ret_to_semax Delta  Q R) s_atoms2)) s_atoms1.
Proof.
  intros. induction s_atoms1.
  - right. constructor.
  - unfold atoms_conn_atoms in H.
    simpl in H. apply Forall_app in H. destruct H.
    specialize (IHs_atoms1 H0).
    destruct IHs_atoms1;auto.
    apply atom_conn_returns_to_semax_inv in H.
    destruct H;auto.
Qed.

(* If tc expr *)
Lemma add_exp_to_pre_tc: forall P a b s_pre (pre':C_partial_pre s_pre), 
  pre_to_semax  Delta P (add_exp_to_Cpre b a pre') ->
  ENTAIL Delta, allp_fun_id Delta && P
  |-- !! (bool_type (typeof a) = true) && 
    tc_expr Delta (Eunop Onotbool a (Ctypes.Tint I32 Signed noattr)).
Proof.
  intros.
  destruct pre', b. simpl in H.
  - apply semax_seq_inv in H. destruct H as [Q' [? ?]].
    apply semax_ifthenelse_inv in H.
    eapply derives_trans;[apply H|].
    solve_andp.
  - apply semax_seq_inv in H. destruct H as [Q' [? ?]].
    apply semax_ifthenelse_inv in H.
    eapply derives_trans;[apply H|].
    solve_andp.
Qed.


Lemma add_exp_to_atom_tc: forall P Q b a normal_atom',
  atom_to_semax Delta P Q (add_exp_to_atom b a normal_atom') ->
  ENTAIL Delta, allp_fun_id Delta && P
  |-- !! (bool_type (typeof a) = true) && 
    tc_expr Delta (Eunop Onotbool a (Ctypes.Tint I32 Signed noattr)).
Proof.
  intros. destruct normal_atom', b.
  - apply semax_seq_inv in H. destruct H as [Q' [? ?]].
    apply semax_ifthenelse_inv in H.
    eapply derives_trans;[apply H|].
    solve_andp.
  - apply semax_seq_inv in H. destruct H as [Q' [? ?]].
    apply semax_ifthenelse_inv in H.
    eapply derives_trans;[apply H|].
    solve_andp.
Qed.


Lemma add_exp_to_return_tc: forall P Q b a return_atom',
  atom_ret_to_semax Delta P Q (add_exp_to_ret_atom b a return_atom') ->
  ENTAIL Delta, allp_fun_id Delta && P
  |-- !! (bool_type (typeof a) = true) && 
    tc_expr Delta (Eunop Onotbool a (Ctypes.Tint I32 Signed noattr)).
Proof.
  intros. destruct return_atom', b.
  - simpl in H.
    apply semax_seq_inv in H. destruct H as [Q' [? ?]].
    replace p with (p ++ nil) in H0 by apply app_nil_r.
    apply path_to_statement_app in H0.
    apply semax_seq_inv in H0. destruct H0 as [Q'' [? ?]].
    apply semax_ifthenelse_inv in H.
    eapply derives_trans;[apply H|].
    solve_andp.
  - simpl in H.
    apply semax_seq_inv in H. destruct H as [Q' [? ?]].
    replace p with (p ++ nil) in H0 by apply app_nil_r.
    apply path_to_statement_app in H0.
    apply semax_seq_inv in H0. destruct H0 as [Q'' [? ?]].
    apply semax_ifthenelse_inv in H.
    eapply derives_trans;[apply H|].
    solve_andp.
Qed.

Lemma if_gen_tc:
  forall b e P Q s_pre1 (c_pre1: C_partial_pres s_pre1) s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1,
  ~ (s_pre1 = [] /\ s_atom_normal1 = [] /\ s_atom_break1 = [] /\ s_atom_continue1 = [] /\ s_atom_return1 = []) -> 
  CForall (@pre_to_semax CS Espec Delta P) (add_exp_to_Cpres b e c_pre1) ->
  Forall (atom_to_semax Delta P (RA_normal Q)) (add_exp_to_atoms b e s_atom_normal1) ->
  Forall (atom_to_semax Delta P (RA_break Q)) (add_exp_to_atoms b e s_atom_break1) ->
  Forall (atom_to_semax Delta P (RA_continue Q)) (add_exp_to_atoms b e s_atom_continue1) ->
  Forall (atom_ret_to_semax Delta P (RA_return Q))
          (add_exp_to_ret_atoms b e s_atom_return1) ->
ENTAIL Delta, allp_fun_id Delta && P
|-- !! (bool_type (typeof e) = true) && tc_expr Delta (Eunop Onotbool e (Ctypes.Tint I32 Signed noattr)).
Proof.
  intros.
  destruct c_pre1 as [|s_pre' c_pre' s_pre1 c_pre1].
  2:{ destruct H0. apply add_exp_to_pre_tc in H0. auto. }
  destruct s_atom_normal1 as [|normal_atom' normal_atom1].
  2:{ inversion H1;subst. apply add_exp_to_atom_tc in H7. auto. }
  destruct s_atom_break1 as [|break_atom' break_atom1].
  2:{ inversion H2;subst. apply add_exp_to_atom_tc in H7. auto. }
  destruct s_atom_continue1 as [|continue_atom' continue_atom1].
  2:{ inversion H3;subst. apply add_exp_to_atom_tc in H7. auto. }
  destruct s_atom_return1 as [|return_atom' return_atom1].
  2:{ inversion H4;subst. apply add_exp_to_return_tc in H7. auto. }
  tauto.
Qed.

(* If-inversions *)

Lemma typed_true_or_typed_false': forall a,
  bool_type (typeof a) = true ->
  ENTAIL Delta, (tc_expr Delta (Eunop Onotbool a (Ctypes.Tint I32 Signed noattr)))
  |-- (local (liftx (typed_true (typeof a)) (eval_expr a))) ||
  (local (liftx (typed_false (typeof a)) (eval_expr a))).
Proof.
  intros.
  unfold liftx. simpl. intros x.
  unfold lift. unfold local.
  unfold lift1.
  unfold typed_true, typed_false.
  Intros. unfold tc_environ in H0.
  pose proof typecheck_expr_sound _ _ a H0.
  eapply derives_trans.
  { apply andp_right. apply derives_refl.
    eapply derives_trans;[|apply H1].
    unfold tc_expr. simpl.
    rewrite denote_tc_assert_andp.
    rewrite andp_unfold. apply andp_left2.
    apply derives_refl.
  }
  apply derives_extract_prop'. intros.
  eapply expr_lemmas.tc_bool_val with (v:= eval_expr a x) in H;auto.
  destruct (strict_bool_val (eval_expr a x) (typeof a)).
  { destruct b.
    - apply orp_right1. apply prop_right. auto.
    - apply orp_right2. apply prop_right. auto.
  }
  destruct H. inv H.
Qed.


(* 

TODO: may not be able to prove this lemma?

because there is no exclued-middle in typed-true &

Lemma typed_false_typed_not_true: forall e,
bool_type (typeof e) = true ->
ENTAIL Delta, (tc_expr Delta (Eunop Onotbool e (Tint I32 Signed noattr))) &&
local (liftx (typed_false (typeof e)) (eval_expr e))
|-- local (liftx (typed_true (typeof (semax_lemmas.Cnot e)))
                (eval_expr (semax_lemmas.Cnot e))).
Proof.
  intros.
  unfold semax_lemmas.Cnot.
  unfold liftx. simpl. intros x.
  unfold lift. unfold local.
  unfold lift1.
  unfold typed_true, typed_false.
  apply derives_extract_prop. intros.
  rewrite andp_comm.  apply derives_extract_prop. intros.
  unfold tc_environ in H0.
  pose proof typecheck_expr_sound _ _ (e) H0.
  pose proof typecheck_expr_sound _ _ (semax_lemmas.Cnot e) H0.
  unfold semax_lemmas.Cnot in H2.
  eapply derives_trans.
  { apply andp_right. 
    { eapply derives_trans;[|apply H2].
      unfold tc_expr. simpl.
      rewrite denote_tc_assert_andp.
      rewrite andp_unfold. apply andp_left2.
      apply derives_refl. }
    { eapply derives_trans;[|apply H3].
      unfold tc_expr. solve_andp. }
  }
  rewrite andp_comm. apply derives_extract_prop;intros.
  apply prop_derives. intros.
  apply expr_lemmas.tc_bool_val in H4;auto.
  destruct H4. destruct x0. auto.
  apply expr_lemmas.tc_bool_val in H5;auto.
  destruct H5. destruct x0.
  { exfalso. congruence. }
  { exfalso. congruence. } *)


Lemma pre_to_semax_if_true_inv_group: forall P e s_pre (c_pre: C_partial_pres s_pre),
CForall (@pre_to_semax  CS Espec Delta P) (add_exp_to_Cpres true e c_pre) ->
CForall (@pre_to_semax CS Espec Delta
     (P && local (liftx (typed_true (typeof e)) (eval_expr e)))) c_pre.
Proof.
  intros.
  induction c_pre.
  + constructor.
  + simpl in H. destruct H. apply IHc_pre in H0.
    split;auto.
    clear - H. induction r'.
    { simpl in H. hnf.
      rename H into H1. simpl in H1.
      eapply semax_seq_inv' in H1.
      apply semax_ifthenelse_inv in H1.
      eapply semax_pre'.
      { rewrite <- !andp_assoc.
        apply andp_derives;[|apply derives_refl].
        rewrite andp_assoc. apply H1.
      }
      rewrite exp_andp2. rewrite exp_andp1. apply semax_extract_exists.
      intros P1. rewrite !andp_assoc. apply semax_extract_prop. intros.
      rewrite andp_comm. rewrite !andp_assoc.
      apply semax_extract_prop. intros [E1 E2].
      rewrite overridePost_normal_split in E1.
      apply semax_skip_inv in E1. rewrite normal_split_assert_elim in E1.
      eapply semax_pre'.
      { rewrite <- !andp_assoc.
        apply andp_derives;[|apply derives_refl].
        rewrite !andp_assoc. apply E1.
      }
      rewrite !exp_andp1. apply semax_extract_exists. intros R.
      rewrite !andp_assoc. apply semax_extract_prop. intros.
      eapply semax_pre'. 2:{ apply H0. }
      solve_andp.
    }
Qed.

Lemma pre_to_semax_if_false_inv_group: forall P e s_pre (c_pre: C_partial_pres s_pre),
CForall (@pre_to_semax  CS Espec Delta P) (add_exp_to_Cpres false e c_pre) ->
CForall (@pre_to_semax CS Espec Delta
     (P && local (liftx (typed_false (typeof e)) (eval_expr e)))) c_pre.
Proof.
  intros.
  induction c_pre.
  + constructor.
  + simpl in H. destruct H. apply IHc_pre in H0.
    split;auto.
    clear - H. induction r'.
    { simpl in H. hnf.
      rename H into H1. simpl in H1.
      eapply semax_seq_inv' in H1.
      apply semax_ifthenelse_inv in H1.
      eapply semax_pre'.
      { rewrite <- !andp_assoc.
        apply andp_derives;[|apply derives_refl].
        rewrite andp_assoc. apply H1.
      }
      rewrite exp_andp2. rewrite exp_andp1. apply semax_extract_exists.
      intros P1. rewrite !andp_assoc. apply semax_extract_prop. intros.
      rewrite andp_comm. rewrite !andp_assoc.
      apply semax_extract_prop. intros [E1 E2].
      rewrite overridePost_normal_split in E1.
      apply semax_skip_inv in E2.
      rewrite overridePost_normal_split in E2.
      rewrite normal_split_assert_elim in E2.
      eapply semax_pre'.
      { rewrite <- !andp_assoc.
        apply andp_derives;[|apply derives_refl].
        rewrite !andp_assoc. apply E2. }
      rewrite !exp_andp1. apply semax_extract_exists. intros R.
      rewrite !andp_assoc. apply semax_extract_prop. intros.
      eapply semax_pre'. 2:{ apply H0. }
      solve_andp.
    }
Qed.


Lemma atom_to_semax_if_true_inv_group: forall P Q e atoms,
Forall (@atom_to_semax  CS Espec Delta P Q) (add_exp_to_atoms true (e) atoms) ->
Forall (@atom_to_semax  CS Espec Delta
    (P && local (liftx (typed_true (typeof e)) (eval_expr e)))
  Q) (atoms).
Proof.
  intros.
  induction atoms.
  + constructor.
  + simpl in H. inv H. apply IHatoms in H3.
    constructor;auto.
    clear - H2. rename H2 into H. destruct a.
    { simpl in H. hnf.
      rename H into H1. simpl in H1.
      eapply semax_seq_inv' in H1.
      apply semax_ifthenelse_inv in H1.
      eapply semax_pre'.
      { rewrite <- !andp_assoc.
        apply andp_derives;[|apply derives_refl].
        rewrite andp_assoc. apply H1.
      }
      rewrite exp_andp2. rewrite exp_andp1. apply semax_extract_exists.
      intros P1. rewrite !andp_assoc. apply semax_extract_prop. intros.
      rewrite andp_comm. rewrite !andp_assoc.
      apply semax_extract_prop. intros [E1 E2].
      rewrite overridePost_normal_split in E1.
      apply semax_skip_inv in E1. rewrite normal_split_assert_elim in E1.
      eapply semax_pre'.
      { rewrite <- !andp_assoc.
        apply andp_derives;[|apply derives_refl].
        rewrite !andp_assoc. apply E1.
      }
      rewrite !exp_andp1. apply semax_extract_exists. intros R.
      rewrite !andp_assoc. apply semax_extract_prop. intros.
      eapply semax_pre'. 2:{ apply H0. }
      solve_andp.
    }
Qed.

Lemma atom_to_semax_if_false_inv_group: forall P Q e atoms,
Forall (@atom_to_semax  CS Espec Delta P Q) (add_exp_to_atoms false e atoms) ->
Forall (@atom_to_semax  CS Espec Delta
    (P && local (liftx (typed_false (typeof e)) (eval_expr e)))
  Q) (atoms).
Proof.
  intros.
  induction atoms.
  + constructor.
  + simpl in H. inv H. apply IHatoms in H3.
    constructor;auto.
    clear - H2. rename H2 into H. destruct a.
    { simpl in H. hnf.
      rename H into H1. simpl in H1.
      eapply semax_seq_inv' in H1.
      apply semax_ifthenelse_inv in H1.
      eapply semax_pre'.
      { rewrite <- !andp_assoc.
        apply andp_derives;[|apply derives_refl].
        rewrite andp_assoc. apply H1.
      }
      rewrite exp_andp2. rewrite exp_andp1. apply semax_extract_exists.
      intros P1. rewrite !andp_assoc. apply semax_extract_prop. intros.
      rewrite andp_comm. rewrite !andp_assoc.
      apply semax_extract_prop. intros [E1 E2].
      rewrite overridePost_normal_split in E1.
      apply semax_skip_inv in E2.
      rewrite overridePost_normal_split in E2.
      rewrite normal_split_assert_elim in E2.
      eapply semax_pre'.
      { rewrite <- !andp_assoc.
        apply andp_derives;[|apply derives_refl].
        rewrite !andp_assoc. apply E2. }
      rewrite !exp_andp1. apply semax_extract_exists. intros R.
      rewrite !andp_assoc. apply semax_extract_prop. intros.
      eapply semax_pre'. 2:{ apply H0. }
      solve_andp.
    }
Qed.

Lemma atom_ret_to_semax_if_true_inv_group: forall P Q e atoms,
Forall (@atom_ret_to_semax CS Espec Delta P Q) (add_exp_to_ret_atoms true (e) atoms) ->
Forall (@atom_ret_to_semax CS Espec Delta 
    (P && local (liftx (typed_true (typeof e)) (eval_expr e)))
  Q) (atoms).
Proof.
  intros.
  induction atoms.
  + constructor.
  + simpl in H. inv H. apply IHatoms in H3.
    constructor;auto.
    clear - H2. rename H2 into H. destruct a.
    { simpl in H. hnf.
      rename H into H1. simpl in H1.

      apply semax_seq_inv in H1. destruct H1 as [Q0 [H3 H2]].
      replace p with (p ++ nil) in H2 by apply app_nil_r.
      apply path_to_statement_app in H2. simpl in H2.
      specialize (semax_seq _ _ _ _ _ _ H3 H2) as H1.
      clear H2 H3 Q0. apply seq_assoc in H1.

      apply semax_seq_inv' in H1.
      apply semax_seq_inv' in H1.
      apply semax_ifthenelse_inv in H1.
      eapply semax_pre'.
      { rewrite <- !andp_assoc.
        apply andp_derives;[|apply derives_refl].
        rewrite andp_assoc. apply H1.
      }
      rewrite exp_andp2. rewrite exp_andp1. apply semax_extract_exists.
      intros P1. rewrite !andp_assoc. apply semax_extract_prop. intros.
      rewrite andp_comm. rewrite !andp_assoc.
      apply semax_extract_prop. intros [E1 E2].
      apply semax_skip_inv in E1.
      rewrite overridePost_overridePost in E1.
      eapply semax_pre'.
      { rewrite <- !andp_assoc.
        apply andp_derives;[|apply derives_refl].
        rewrite !andp_assoc. apply E1.
      }
      rewrite overridePost_normal'.
      rewrite !exp_andp1. apply semax_extract_exists. intros R.
      rewrite !andp_assoc. apply semax_extract_prop. intros.
      replace p with (p ++ nil) by apply app_nil_r.
      apply path_to_statement_app. simpl path_to_statement.
      eapply semax_seq with (Q0:=(EX Q0 : environ -> mpred,
        !! semax Delta Q0 (Clight.Sreturn o) (return_split_assert Q) && Q0)
      ).
      { eapply semax_conseq;[..|apply H0];try intros; solve_andp. }
      apply semax_extract_exists. intros R0.
      apply semax_extract_prop. intros. auto.
    }
Qed.


Lemma atom_ret_to_semax_if_false_inv_group: forall P Q e atoms,
Forall (@atom_ret_to_semax  CS Espec Delta P Q) (add_exp_to_ret_atoms false e atoms) ->
Forall (@atom_ret_to_semax  CS Espec Delta
    (P && local (liftx (typed_false (typeof e)) (eval_expr e)))
  Q) (atoms).
Proof.
  intros.
  induction atoms.
  + constructor.
  + simpl in H. inv H. apply IHatoms in H3.
    constructor;auto.
    clear - H2. rename H2 into H. destruct a.
    { simpl in H. hnf.
      rename H into H1. simpl in H1.

      apply semax_seq_inv in H1. destruct H1 as [Q0 [H3 H2]].
      replace p with (p ++ nil) in H2 by apply app_nil_r.
      apply path_to_statement_app in H2. simpl in H2.
      specialize (semax_seq _ _ _ _ _ _ H3 H2) as H1.
      clear H2 H3 Q0. apply seq_assoc in H1.
      
      eapply semax_seq_inv' in H1.
      eapply semax_seq_inv' in H1.
      apply semax_ifthenelse_inv in H1.
      eapply semax_pre'.
      { rewrite <- !andp_assoc.
        apply andp_derives;[|apply derives_refl].
        rewrite andp_assoc. apply H1.
      }
      rewrite exp_andp2. rewrite exp_andp1. apply semax_extract_exists.
      intros P1. rewrite !andp_assoc. apply semax_extract_prop. intros.
      rewrite andp_comm. rewrite !andp_assoc.
      apply semax_extract_prop. intros [E1 E2].
      apply semax_skip_inv in E2.
      rewrite overridePost_overridePost in E2.
      eapply semax_pre'.
      { rewrite <- !andp_assoc.
        apply andp_derives;[|apply derives_refl].
        rewrite !andp_assoc. apply E2.
      }
      rewrite overridePost_normal'.
      rewrite !exp_andp1. apply semax_extract_exists. intros R.
      rewrite !andp_assoc. apply semax_extract_prop. intros.
      replace p with (p ++ nil) by apply app_nil_r.
      apply path_to_statement_app. simpl path_to_statement.
      eapply semax_seq with (Q0:=(EX Q0 : environ -> mpred,
        !! semax Delta Q0 (Clight.Sreturn o) (return_split_assert Q) && Q0)
      ).
      { eapply semax_conseq;[..|apply H0];try intros; solve_andp. }
      apply semax_extract_exists. intros R0.
      apply semax_extract_prop. intros. auto.
    }
Qed.

End SemanticsProofs.

