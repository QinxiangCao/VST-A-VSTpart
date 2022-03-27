Require Export CSplit.AClight.

Require Import VST.floyd.proofauto.
Require Import CSplit.strong.

Fixpoint CForall {A:Type} {binder: A -> Type} 
(P : forall (a: A), binder a -> Prop ) {sl: list A}
(cl : @list_binded_of A binder sl) : Prop :=
match cl with
| {} => True
| list_binded_cons sx cx sl' cl' =>
    P sx cx /\ CForall P cl'
end.

(* Fixpoint CIn {A:Type} {binder: A -> Type}
  {sx: A} (cx: binder sx) 
  (sl: list A) (cl: @list_binded_of A binder sl) : Prop.
  (* match cl with
  | list_binded_nil => False
  | list_binded_cons sx' cx' sl' cl' =>
      sx = sx' /\ cx = cx' /\ CIn cx' sl' cl'
  end. *)
Admitted.


Lemma CForall_forall {A:Type} {binder: A -> Type}:
  forall (P : forall (a: A), binder a -> Prop ) {sl: list A}  
  (cl: @list_binded_of A binder sl),
  CForall P cl <-> 
    (forall (sx: A) (cx : binder sx), CIn cx sl cl -> P sx cx).
Admitted. *)



Section Semantics.

Context {CS: compspecs} {Espec: OracleKind} (Delta: tycontext).

Fixpoint to_Clight  (a: atom_statement) : Clight.statement :=
match a with
| Askip => Clight.Sskip
| Aassign e1 e2 => Clight.Sassign e1 e2
| Aset id e => Clight.Sset id e
| Acall id e elis => Clight.Scall id e elis
end.

Definition split_atom_to_statement (x : (expr + atom_statement)):=
  match x with
  | inl e => (Clight.Sifthenelse e Clight.Sskip Clight.Sbreak)
  | inr s => to_Clight s
  end.

Fixpoint path_to_statement (p:path):  Clight.statement :=
  match p with
  | nil => Clight.Sskip
  | inl e :: p' => Clight.Ssequence 
              (Clight.Sifthenelse e Clight.Sskip Clight.Sbreak) 
              (path_to_statement p')
  | inr s :: p' => Clight.Ssequence
              (to_Clight s) (path_to_statement p')
  end.

(* Fixpoint path_to_statement'  (p:path):  Clight.statement :=
    fold_Ssequence (map split_atom_to_statement p). *)



Lemma path_to_statement_app: forall P Q l1 l2,
  semax Delta P (Clight.Ssequence (path_to_statement l1)
    (path_to_statement l2)) Q <->
    semax Delta P (path_to_statement (l1++l2)) Q.
Proof.
  intros. revert P. induction l1.
  { intros. simpl. split;intro.
    + apply semax_seq_inv in H.
      destruct H as [R1 [E1 E3]].
      apply semax_skip_inv in E1.
      eapply semax_pre' with (P':=RA_normal (overridePost R1 Q)).
      { eapply derives_trans;[|apply E1]. solve_andp. }
      unfold overridePost. unfold RA_normal. destruct Q. auto.
    + eapply semax_seq. 2:{ apply H. } 
      destruct Q;unfold_der.
      eapply semax_simple_inv with (Post:=normal_ret_assert P);auto.
      constructor.
  }
  { intros. destruct a; simpl.
    { split;intro.
      + apply semax_seq_inv in H.
        destruct H as [R2 [E1 E3]].
        apply semax_seq_inv in E1.
        destruct E1 as [R1 [E1 E2]].
        pose proof semax_seq _ _ _ _ _ _ E2 E3.
        apply IHl1 in H.
        eapply semax_seq with (Q0:=R1);auto.
        rewrite overridePost_overridePost in E1.
        auto.
      + apply semax_seq_inv in H.
        destruct H as [R1 [E1 E3]].
        apply IHl1 in E3.
        apply semax_seq_inv in E3.
        destruct E3 as [R2 [E2 E3]].
        eapply semax_seq.
        { eapply semax_seq.
          + rewrite overridePost_overridePost. apply E1.
          + apply E2. }
        apply E3.
    }
    { split;intro.
      + apply semax_seq_inv in H.
        destruct H as [R2 [E1 E3]].
        apply semax_seq_inv in E1.
        destruct E1 as [R1 [E1 E2]].
        pose proof semax_seq _ _ _ _ _ _ E2 E3.
        apply IHl1 in H.
        eapply semax_seq with (Q0:=R1);auto.
        rewrite overridePost_overridePost in E1.
        auto.
      + apply semax_seq_inv in H.
        destruct H as [R1 [E1 E3]].
        apply IHl1 in E3.
        apply semax_seq_inv in E3.
        destruct E3 as [R2 [E2 E3]].
        eapply semax_seq.
        { eapply semax_seq.
          + rewrite overridePost_overridePost. apply E1.
          + apply E2. }
        apply E3.
    }
  }
Qed.


Fixpoint path_to_semax { s_path: S_full_path }
  (c_path: C_full_path s_path) : Prop :=
  match c_path with
  | mk_C_full_path pre path post =>
      @semax CS Espec Delta pre (path_to_statement path)
      (normal_ret_assert post)
  | bind_C_full_path A HA s_path' c_path' =>
      forall (a:A), path_to_semax (c_path' a)
  end.

Fixpoint post_to_semax post { s_post : S_partial_post }
  (c_post: C_partial_post s_post) : Prop :=
  match c_post with
  | mk_C_partial_post pre path =>
      @semax CS Espec Delta pre (path_to_statement path)
      (normal_ret_assert post)
  | bind_C_partial_post A HA s_post' c_post' =>
      forall (a:A), post_to_semax post (c_post' a)
  end.

Fixpoint pre_to_semax pre { s_pre : S_partial_pre }
  (c_pre: C_partial_pre s_pre) : Prop :=
  match c_pre with
  | mk_C_partial_pre path post =>
      @semax CS Espec Delta pre (path_to_statement path)
      (normal_ret_assert post)
  (* | bind_C_partial_pre A HA s_pre' c_pre' =>
      forall (a:A), pre_to_semax pre (c_pre' a) *)
  end.


Definition return_ret_assert (Q: option val -> environ->mpred) : ret_assert :=
  {| RA_normal := seplog.FF; RA_break := seplog.FF; RA_continue := seplog.FF; RA_return := Q |}.


Fixpoint post_ret_to_semax post { s_post : S_partial_post_ret }
  (c_post: C_partial_post_ret s_post) : Prop :=
  match c_post with
  | mk_C_partial_post_ret pre path retval =>
      @semax CS Espec Delta pre 
        (Clight.Ssequence 
          (path_to_statement path)
          (Clight.Sreturn retval))
      (return_ret_assert post)
  | bind_C_partial_post_ret A HA s_post' c_post' =>
      forall (a:A), post_ret_to_semax post (c_post' a)
  end.

Definition atom_to_semax pre post atom := 
  match atom with
  | mk_atom path =>
      @semax CS Espec Delta pre 
        (path_to_statement path)
        (normal_ret_assert post)
  end.


Definition atom_ret_to_semax pre post atom := 
  match atom with
  | mk_atom_ret path retval =>
      @semax CS Espec Delta pre 
        (Clight.Ssequence (path_to_statement path) 
          (Clight.Sreturn retval))
        (return_ret_assert (post))
  end.


Definition split_Semax (P: assert) (Q: ret_assert) {s_res: S_result} : (C_result s_res) -> Prop :=
  match s_res with
  | None => fun _ => False
  | Some (mk_S_result_rec s_pre s_path
      s_post_normal s_post_break s_post_continue s_post_return
      s_atom_normal s_atom_break s_atom_continue s_atom_return) =>
      fun c_res =>
      match c_res with
      | mk_C_result_rec c_pre c_path
          c_post_normal c_post_break c_post_continue c_post_return =>
          CForall (@pre_to_semax P) c_pre
        /\ CForall (@path_to_semax) c_path
        /\ CForall (@post_to_semax (RA_normal Q)) c_post_normal
        /\ CForall (@post_to_semax (RA_break Q)) c_post_break
        /\ CForall (@post_to_semax (RA_continue Q)) c_post_continue
        /\ CForall (@post_ret_to_semax (RA_return Q)) c_post_return
        /\ Forall (atom_to_semax P (RA_normal Q)) s_atom_normal
        /\ Forall (atom_to_semax P (RA_break Q)) s_atom_break
        /\ Forall (atom_to_semax P (RA_continue Q)) s_atom_continue
        /\ Forall (atom_ret_to_semax P (RA_return Q)) s_atom_return
      end
  end.

Lemma pre_to_semax_derives: forall P Q s_pre 
  (c_pre: C_partial_pre s_pre),
  ENTAIL Delta, ((allp_fun_id Delta) && Q) |--  P ->
  pre_to_semax P c_pre ->
  pre_to_semax Q c_pre.
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
  pre_to_semax P c_pre ->
  pre_to_semax Q c_pre.
Proof.
  intros.
  eapply pre_to_semax_derives;[|apply H0].
  eapply derives_trans;[|apply H];solve_andp.
Qed.

Lemma post_to_semax_derives: forall P Q s_post
  (c_post: C_partial_post s_post),
  ENTAIL Delta, Q |--  P ->
  post_to_semax Q c_post ->
  post_to_semax P c_post.
Proof.
  intros. induction c_post.
  + simpl in H0. simpl.
    eapply semax_conseq with (P':=pre)(R':= normal_ret_assert Q);auto;
    unfold normal_ret_assert, RA_normal, RA_break, RA_continue, RA_return;
    intros;try solve_andp.
    { eapply derives_trans;[|apply H]. solve_andp. }
  + simpl in *. auto.
Qed.

Lemma post_ret_to_semax_derives: forall P Q s_post
  (c_post: C_partial_post_ret s_post),
  (forall v, ENTAIL Delta, Q v |--  P v) ->
  post_ret_to_semax Q c_post ->
  post_ret_to_semax P c_post.
Proof.
  intros. induction c_post.
  + simpl in H0. simpl.
    eapply semax_conseq with (P':=pre)(R':= return_ret_assert Q);auto;
    unfold return_ret_assert, RA_normal, RA_break, RA_continue, RA_return;
    intros;try solve_andp.
    { eapply derives_trans;[|apply H]. solve_andp. }
  + simpl in *. auto.
Qed.

Lemma atom_to_semax_derives: forall P1 P2 Q1 Q2 a,
  P2 |-- P1 ->
  ENTAIL Delta, Q1 |-- Q2 ->
  atom_to_semax P1 Q1 a ->
  atom_to_semax P2 Q2 a.
Proof.
  intros. destruct a;simpl.
  eapply semax_conseq with (P':=P1)(R':=normal_ret_assert Q1);auto;
  unfold normal_ret_assert, RA_normal, RA_break, RA_continue, RA_return;
  intros;try solve_andp.
  - eapply derives_trans;[|apply H]. solve_andp. 
  - eapply derives_trans;[|apply H0]. solve_andp.
Qed.

Lemma atom_return_to_semax_derives: forall P1 P2 Q1 Q2 a,
  P2 |-- P1 ->
  (forall v, ENTAIL Delta, Q1 v  |-- Q2 v ) ->
  atom_ret_to_semax P1 Q1 a ->
  atom_ret_to_semax P2 Q2 a.
Proof.
  intros. destruct a as [p r].
  eapply semax_conseq with (P':=P1)(R':=return_ret_assert Q1);
  unfold return_ret_assert;auto;
  unfold RA_normal, RA_break, RA_continue, RA_return;
  intros;try solve_andp.
  - eapply derives_trans;[|apply H]. solve_andp.
  - eapply derives_trans;[|apply H0]. solve_andp.
Qed.

Lemma pre_to_semax_sem: forall (s_pre: S_partial_pre)
  (c_pre: C_partial_pre s_pre),
  (pre_to_semax
        (EX Q : assert,
          !! (pre_to_semax Q c_pre) && Q)) 
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
  post_to_semax R (Cpost_conn_atom c_post atom) ->
  post_to_semax (EX Q, Q && !! ( atom_to_semax Q R atom)) c_post.
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
  - simpl. intros. simpl in H. specialize (H a). apply H0 in H. auto.
Qed.

Lemma path_conn_to_semax_reverse_simple: forall { s_pre }
  (c_pre: C_partial_pre s_pre) a1,
  path_to_semax (add_P_to_Cpre a1 c_pre) ->
    pre_to_semax a1 c_pre.
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
atom_ret_to_semax P2 Q p ->
atom_ret_to_semax P1 Q p.
Proof.
 intros.
 eapply atom_return_to_semax_derives.
 { apply H. }
 { intros. solve_andp. }
 { auto. }
Qed.

Lemma atom_return_to_semax_derives_post: forall p P Q1 Q2,
(forall v, ENTAIL Delta, Q1 v |-- Q2 v) ->
atom_ret_to_semax P Q1 p ->
atom_ret_to_semax P Q2 p.
Proof.
 intros.
 eapply atom_return_to_semax_derives.
 { apply derives_refl. }
 { intros. apply H. }
 { auto. }
Qed.

Lemma atom_return_to_semax_derives_pre_group: forall P1 P2 Q atoms,
  P1 |-- P2 ->
  Forall (atom_ret_to_semax P2 Q) atoms ->
  Forall (atom_ret_to_semax P1 Q) atoms.
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
  CForall (@pre_to_semax P2) c_pres ->
  CForall (@pre_to_semax P1) c_pres.
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
  CForall (@pre_to_semax P2) c_pres ->
  CForall (@pre_to_semax P1) c_pres.
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
  CForall (@post_to_semax Q1) c_posts ->
  CForall (@post_to_semax Q2) c_posts.
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
  CForall (@post_ret_to_semax Q1) c_posts ->
  CForall (@post_ret_to_semax Q2) c_posts.
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
  atom_to_semax P2 Q p ->
  atom_to_semax P1 Q p.
Proof.
  intros.
  eapply atom_to_semax_derives.
  - apply H.
  - solve_andp.
  - auto.
Qed.

Lemma atom_to_semax_derives_pre_group: forall P1 P2 Q atoms,
  P1 |-- P2 ->
  Forall (atom_to_semax P2 Q) atoms ->
  Forall (atom_to_semax P1 Q) atoms.
Proof. 
  intros.
  eapply Forall_forall.
  intros. eapply atom_to_semax_derives_pre.
  apply H. eapply Forall_forall in H0. apply H0. auto.
Qed.

Lemma atom_to_semax_derives_post: forall p P Q1 Q2,
  ENTAIL Delta, Q1 |-- Q2 ->
  atom_to_semax P Q1 p ->
  atom_to_semax P Q2 p.
Proof.
  intros.
  eapply atom_to_semax_derives.
  - apply derives_refl.
  - apply H.
  - auto.
Qed.

Lemma atom_to_semax_derives_post_group: forall p P Q1 Q2,
  ENTAIL Delta, Q1 |-- Q2 ->
  Forall (atom_to_semax P Q1) p ->
  Forall (atom_to_semax P Q2) p.
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
  Forall (atom_ret_to_semax P Q1) p ->
  Forall (atom_ret_to_semax P Q2) p.
Proof.
  intros. induction p.
  - constructor.
  -  inv H0. apply IHp in H4.
    constructor; auto.
    eapply atom_return_to_semax_derives_post;[|apply H3].
    auto.
Qed.


Lemma pre_to_semax_sem_group: forall (s_pres: S_partial_pres)
  (c_pres: C_partial_pres s_pres),
  (CForall (@pre_to_semax
        (EX Q, Q && !! (CForall (@pre_to_semax Q) c_pres))) 
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
 (atom_to_semax 
        (EX Q : assert,
          !! (atom_to_semax Q R x) && Q)) R
      x.
Proof.
  intros. destruct x.
  apply semax_extract_exists. intros Q.
  apply semax_extract_prop.
  intros. auto.
Qed.
  
Lemma atom_return_to_semax_sem: forall x R,
 (atom_ret_to_semax 
        (EX Q : assert,
          !! (atom_ret_to_semax Q R x) && Q)) R
      x.
Proof.
  intros. destruct x as [p v].
  apply semax_extract_exists. intros Q.
  apply semax_extract_prop.
  intros. auto.
Qed.


Lemma atom_to_semax_sem_group: forall xs R,
 Forall (atom_to_semax (EX Q : assert, !! Forall (atom_to_semax Q R) xs && Q) R) xs.
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
 Forall (atom_ret_to_semax 
  (EX Q : assert, !! Forall (atom_ret_to_semax Q R) xs && Q) R) xs.
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

Lemma post_to_semax_conj_rule: forall Q1 Q2 s_post
  (c_post : C_partial_post s_post),
post_to_semax Q1 c_post ->
post_to_semax Q2 c_post ->
post_to_semax (Q1 && Q2) c_post.
Proof.
  intros.
  induction c_post.
  - simpl in *.
    eapply semax_conseq.
    6: { eapply semax_conj_rule with 
          (Q1:= normal_ret_assert Q1) 
          (Q2:= normal_ret_assert Q2).
        apply H. apply H0. }
    { solve_andp. }
    { solve_andp. }
    { solve_andp. }
    { solve_andp. }
    { intros. solve_andp. }
  - simpl in *. auto.
Qed.


Lemma post_to_semax_conj_rule_group: forall Q1 Q2 s_posts
  (c_posts : C_partial_posts s_posts),
CForall (@post_to_semax Q1) c_posts ->
CForall (@post_to_semax Q2) c_posts ->
CForall (@post_to_semax (Q1 && Q2)) c_posts.
Proof.
  intros.
  induction c_posts.
  - constructor.
  - destruct H. destruct H0.
    specialize (IHc_posts H1 H2).
    constructor;auto.
    apply post_to_semax_conj_rule;auto.
Qed.

Lemma atom_to_semax_conj_rule: forall P Q1 Q2 atom,
  atom_to_semax P Q1 atom ->
  atom_to_semax P Q2 atom ->
  atom_to_semax P (Q1 && Q2) atom.
Proof.
  intros. destruct atom. unfold atom_to_semax in *.
  eapply semax_conseq.
  6: { eapply semax_conj_rule with 
  (Q1:= normal_ret_assert Q1) 
  (Q2:= normal_ret_assert Q2).
    apply H. apply H0. }
  { solve_andp. }
  { solve_andp. }
  { solve_andp. }
  { solve_andp. }
  { intros. solve_andp. }
Qed.

Lemma atom_to_semax_conj_rule_group: forall P Q1 Q2 atoms,
  Forall (atom_to_semax P Q1) atoms ->
  Forall (atom_to_semax P Q2) atoms ->
  Forall (atom_to_semax P (Q1 && Q2)) atoms.
Proof.
  intros. induction atoms;auto.
  inversion H;subst.
  inversion H0;subst.
  specialize (IHatoms H4 H6).
  pose proof atom_to_semax_conj_rule _ _ _ _ H3 H5.
  constructor;auto.
Qed.

End Semantics.