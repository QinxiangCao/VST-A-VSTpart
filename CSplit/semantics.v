Require Export Csplit.AClight.

(* Require Import VST.floyd.proofauto. *)
Require Import Csplit.strong.

Open Scope aclight_scope.

Definition normal_split_assert Q := {|
RA_normal := Q;
RA_break := seplog.TT; 
RA_continue := seplog.TT; 
RA_return := fun _ => TT;
|}.

Definition return_split_assert (Q: option val -> environ->mpred) : ret_assert :=
  {| RA_normal := seplog.TT; 
     RA_break := seplog.TT; 
     RA_continue := seplog.TT; 
     RA_return := Q |}.

Lemma normal_split_assert_elim: forall P,
  RA_normal (normal_split_assert P) = P.
Proof.
  intros. reflexivity.
Qed.


Lemma overridePost_normal_split: forall P Q,
  overridePost P (normal_split_assert Q) = normal_split_assert P.
Proof. intros. reflexivity. Qed.

Fixpoint SForall {A:Type} 
(P : A -> Prop ) (sl: list A) : Prop :=
match sl with
| nil => True
| x :: sl' =>  P x  /\ SForall P sl'
end.

Fixpoint CForall {A:Type} {binder: A -> Type} 
(P : forall (a: A), binder a -> Prop ) {sl: list A}
(cl : @list_binded_of A binder sl) : Prop :=
match cl with
| {} => True
| list_binded_cons sx cx sl' cl' =>
    P sx cx /\ CForall P cl'
end.


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
    + simpl in H. destruct H.
      apply IHcl1 in H0. destruct H0.
       simpl in H. repeat split;try constructor; auto.
    + simpl. destruct H.
      destruct H.
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


Ltac destruct_FForalls :=
  repeat (
    match goal with
    | [H : CForall ?P (_ +++ _) |- _] => 
        let n1 := fresh H in
        apply CForall_Capp in H; destruct H as [H n1]
    | [H : Forall ?P (_ ++ _) |- _] => 
        let n1 := fresh H in
        apply Forall_app in H; destruct H as [H n1]
    end
  ).


Lemma CForall_impl: forall {A:Type} {binder: A -> Type} 
(P : forall (a: A), binder a -> Prop )
(Q : forall (a: A), binder a -> Prop )
{sl: list A} (cl: @list_binded_of A binder sl),
(forall s (c: binder s), P s c -> Q s c) ->
CForall P cl -> CForall Q cl.
Proof.
  intros.
  induction cl.
  - constructor.
  - destruct H0.
    constructor;auto.
Qed.

Lemma CForall_conj: forall {A:Type} {binder: A -> Type} 
(P : forall (a: A), binder a -> Prop )
(Q : forall (a: A), binder a -> Prop )
{sl: list A} (cl: @list_binded_of A binder sl),
CForall P cl -> CForall Q cl -> CForall (fun s c => P s c /\ Q s c) cl.
Proof.
  intros.
  induction cl.
  - constructor.
  - destruct H0. destruct H.
    constructor;auto.
Qed.


Section Semantics.

Context {CS: compspecs} {Espec: OracleKind} (Delta: tycontext).

Definition to_Clight  (a: atom_statement) : Clight.statement :=
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

Fixpoint path_to_statement (p: path) (tail: Clight.statement): Clight.statement :=
  match p with
  | nil => tail
  | inl (true, e) :: p' => Clight.Ssequence 
              (Clight.Sifthenelse e Clight.Sskip Clight.Sbreak) 
              (path_to_statement p' tail)
  | inl (false, e) :: p' => Clight.Ssequence 
              (Clight.Sifthenelse e Clight.Sbreak Clight.Sskip) 
              (path_to_statement p' tail) 
  | inr s :: p' => Clight.Ssequence
              (to_Clight s) (path_to_statement p' tail)
  end.

Lemma nocontinue_split_result: forall c tail,
  nocontinue tail = true ->
  nocontinue (path_to_statement c tail) = true.
Proof.
  intros ? ? H99.
  induction c.
  + simpl.
    auto.
  + destruct a.
    - destruct p, b; simpl; auto.
    - simpl.
      destruct a; auto.
Qed.

Lemma noreturn_split_result: forall c tail,
  noreturn tail = true ->
  noreturn (path_to_statement c tail) = true.
Proof.
  intros.
  induction c.
  + simpl.
    auto.
  + destruct a.
    - destruct p, b; simpl; auto.
    - simpl.
      destruct a; auto.
Qed.

Lemma path_to_statement_app: forall P Q l1 l2 tail,
  semax Delta P
    (Clight.Ssequence
      (path_to_statement l1 Clight.Sskip)
      (path_to_statement l2 tail)) Q
  <-> semax Delta P (path_to_statement (l1 ++ l2) tail) Q.
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
        destruct p, b.
        { apply semax_seq_inv in E1.
          destruct E1 as [R1 [E1 E2]].
          pose proof semax_seq _ _ _ _ _ _ E2 E3.
          apply IHl1 in H.
          eapply semax_seq with (Q0:=R1);auto.
          rewrite overridePost_overridePost in E1.
          auto. }
        { apply semax_seq_inv in E1.
          destruct E1 as [R1 [E1 E2]].
          pose proof semax_seq _ _ _ _ _ _ E2 E3.
          apply IHl1 in H.
          eapply semax_seq with (Q0:=R1);auto.
          rewrite overridePost_overridePost in E1.
          auto. }
      + destruct p, b.
        { apply semax_seq_inv in H.
          destruct H as [R1 [E1 E3]].
          apply IHl1 in E3.
          apply semax_seq_inv in E3.
          destruct E3 as [R2 [E2 E3]].
          eapply semax_seq.
          { eapply semax_seq.
            + rewrite overridePost_overridePost. apply E1.
            + apply E2. }
          apply E3. }
        { apply semax_seq_inv in H.
          destruct H as [R1 [E1 E3]].
          apply IHl1 in E3.
          apply semax_seq_inv in E3.
          destruct E3 as [R2 [E2 E3]].
          eapply semax_seq.
          { eapply semax_seq.
            + rewrite overridePost_overridePost. apply E1.
            + apply E2. }
          apply E3. }
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
      @semax CS Espec Delta pre (path_to_statement path Clight.Sskip)
      (normal_split_assert post)
  | bind_C_full_path A s_path' c_path' =>
      forall (a:A), path_to_semax (c_path' a)
  end.

Definition post_to_semax post { s_post : S_partial_post }
  (c_post: C_partial_post s_post) : Prop :=
  match c_post with
  | mk_C_partial_post pre path =>
      @semax CS Espec Delta pre (path_to_statement path Clight.Sskip)
      (normal_split_assert post)
  end.

Definition pre_to_semax pre { s_pre : S_partial_pre }
  (c_pre: C_partial_pre s_pre) : Prop :=
  match c_pre with
  | mk_C_partial_pre path post =>
      @semax CS Espec Delta pre (path_to_statement path Clight.Sskip)
      (normal_split_assert post)
  end.




Definition post_ret_to_semax post { s_post : S_partial_post_ret }
  (c_post: C_partial_post_ret s_post) : Prop :=
  match c_post with
  | mk_C_partial_post_ret pre path retval =>
      @semax CS Espec Delta pre 
        (path_to_statement path (Clight.Sreturn retval))
      (return_split_assert post)
  end.

Definition atom_to_semax pre post atom := 
  match atom with
  | mk_atom path =>
      @semax CS Espec Delta pre 
        (path_to_statement path Clight.Sskip)
        (normal_split_assert post)
  end.


Definition atom_ret_to_semax pre post atom := 
  match atom with
  | mk_atom_ret path retval =>
      @semax CS Espec Delta pre 
        (path_to_statement path (Clight.Sreturn retval))
        (return_split_assert (post))
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

Definition split_Semax_fun (P: assert) (Q: ret_assert) 
  {s_res: S_result} : (C_result s_res) -> Prop :=
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
        /\ SForall (atom_to_semax P (RA_normal Q)) s_atom_normal
        /\ SForall (atom_to_semax P (RA_break Q)) s_atom_break
        /\ SForall (atom_to_semax P (RA_continue Q)) s_atom_continue
        /\ SForall (atom_ret_to_semax P (RA_return Q)) s_atom_return
      end
  end.

Lemma SForall_equiv: forall {A:Type} P (ls:list A),
  SForall P ls <-> Forall P ls.
Proof.
  intros. split;intro.
  - induction ls;auto. inversion H;subst.
    constructor;auto.
  - induction H;simpl;auto.
Qed.


Theorem split_Semax_fun_equiv: 
  forall (P: assert) (Q: ret_assert) 
  (s_res: S_result) (c_res: C_result s_res),
  split_Semax_fun P Q c_res <-> split_Semax P Q c_res.
Proof.
  intros. destruct s_res.
  - destruct s. destruct c_res. split.
    + intros. destruct H as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
      repeat split;auto;try solve [apply SForall_equiv;auto].
    + intros. destruct H as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
      repeat split;auto;try solve [apply SForall_equiv;auto].
  - destruct c_res. simpl. tauto.
Qed.


End Semantics.
