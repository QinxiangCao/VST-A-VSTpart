Require Import AClight.AClight.
Require Import VST.floyd.proofauto.
Require Import Split.vst_ext.
Notation "x ;; y" := (Ssequence x y)  (at level 65) : logic.

Axiom classic: forall P,  P \/ ~ P.

Inductive atom_statement : Type :=
| Sskip : atom_statement                   (**r do nothing *)
| Sassign : expr -> expr -> atom_statement (**r assignment [lvalue = rvalue] *)
| Sset : ident -> expr -> atom_statement   (**r assignment [tempvar = rvalue] *)
| Scall: option ident -> expr 
          -> list expr -> atom_statement   (**r function call *).

Definition path:= list (expr + atom_statement) .

Definition Non_empty_Type (A:Type): Prop := exists a:A, True.

Inductive split_assert: Type :=
(* the assert of a path *)
| Basic_assert : assert -> assert -> split_assert
| Given_assert (A:Type) (HA: Non_empty_Type A ): 
    (A -> split_assert) -> split_assert 
    (* the type A matches an EX in the pre-condition *)
| Binded_assert (A:Type) (HA: Non_empty_Type A ): 
    (A -> split_assert) -> split_assert
    (* the type A means a universal quantifier over the triple *).

Definition path_statement : Type :=
  split_assert * path.

Inductive partial_assert: Type :=
(* the assert of a partial_path *)
| Basic_partial : assert  -> partial_assert
| Binded_partial (A:Type) (HA: Non_empty_Type A ) :
    (A -> partial_assert) -> partial_assert.

Definition partial_path_statement : Type :=
  partial_assert * path.

Definition return_post_statement : Type := 
  partial_assert * path * option expr.

Definition return_path_atom : Type := path * option expr.
Definition path_statements := list path_statement.
Definition partial_path_statements := list partial_path_statement.
Definition return_post_statements := list return_post_statement.
Definition atom_statements := (list path)%type.
Definition return_atom_statements := (list return_path_atom)%type.

Record split_result:Type := Pack{
  pre   : partial_path_statements;
  paths : path_statements;
  normal_post  : partial_path_statements;
  continue_post: partial_path_statements;
  break_post   : partial_path_statements;
  return_post  : return_post_statements;
  normal_atom  : atom_statements;
  continue_atom: atom_statements;
  break_atom   : atom_statements;
  return_atom  : return_atom_statements;
}.

Definition FALSE := (PROP (False) LOCAL () SEP ()).


(** Define connection between partial paths *)
Fixpoint basic_assert_conn_bind (a1:assert) (a2: partial_assert) : split_assert :=
  match a2 with
  | Basic_partial a2 => (Basic_assert a1 a2)
  | Binded_partial X HX a2' => (Binded_assert X HX (fun x:X => basic_assert_conn_bind
                                                             a1 (a2' x)))
  end.

Fixpoint bind_assert_conn_basic (a2:assert) (a1: partial_assert) : split_assert :=
  match a1 with
  | Basic_partial a1 => (Basic_assert a1 a2)
  | Binded_partial X HX a1' => (Given_assert X HX (fun x:X => bind_assert_conn_basic
                                                            a2 (a1' x)))
  end.


Definition post_conn_bind_pre (pre:partial_path_statement) (p1: path) (a1: assert): path_statement :=
  match pre with (a2, p2) =>
    (basic_assert_conn_bind a1 a2, p1 ++ p2)
  end.


Fixpoint bind_post_conn_pre (post: partial_path_statement) (p2: path) (a2: assert): path_statement :=
  match post with (a1, p1) =>
                  (bind_assert_conn_basic a2 a1, p1 ++ p2)
  end.


Fixpoint posts_conn_pre (posts: partial_path_statements) (pre:partial_path_statement): path_statements :=
  (* posts  + pre, posts have to be basic, pre can be binded*)
  match posts with
  | (Basic_partial a1, p1)::posts' =>
    match p1, pre with
    | [], (Binded_partial _ _ _, _) =>
      (post_conn_bind_pre pre p1 a1)::(posts_conn_pre posts' pre)
    | _, (Basic_partial _, _) =>
      (post_conn_bind_pre pre p1 a1)::(posts_conn_pre posts' pre)
    | _, _  => (posts_conn_pre posts' pre)
    end
  | (Binded_partial X HX a1, p1)::posts' =>
    match pre with
    | (Basic_partial a2, p2) =>
      (bind_post_conn_pre (Binded_partial X HX a1, p1) p2 a2)
        ::(posts_conn_pre posts' pre)
    | _ => posts_conn_pre posts' pre
    end
  | nil => nil
  end.

Definition posts_conn_pres (posts pres: partial_path_statements) : path_statements :=
  flat_map (posts_conn_pre posts) pres.



(** Define connection between partial paths and atoms *)
Definition post_conn_atom (post:partial_path_statement) (p2: path): partial_path_statement :=
  match post with (a1, p1) =>
    (a1, p1 ++ p2)
  end.

Definition post_conn_return (post:partial_path_statement) (p2: path) (r: option expr): return_post_statement :=
  match post with (a1, p1) =>
    (a1, p1 ++ p2, r)
  end.

Definition posts_conn_returns (posts: partial_path_statements) (rets: return_atom_statements) :
  return_post_statements :=
  flat_map (fun post => 
    map (
      fun ret_atom => post_conn_return post (fst ret_atom) (snd ret_atom)) rets
  ) posts.

Definition posts_conn_atoms (posts: partial_path_statements) (atoms: atom_statements) :
partial_path_statements :=
flat_map (fun post => 
  map (post_conn_atom post) atoms
) posts.

Definition atom_conn_pre (p1:path) (pre: partial_path_statement) : partial_path_statement:=
  match pre with (a2, p2) =>
    (a2, p1 ++ p2)
  end.

Definition atoms_conn_pres (atoms: atom_statements) (pres: partial_path_statements) :
partial_path_statements :=
flat_map (fun atom => 
  map (atom_conn_pre atom) pres
) atoms.

Definition atoms_conn_atoms (atom1: atom_statements)
 (atom2: atom_statements) : atom_statements :=
   flat_map (fun p1 => map (app p1) atom2) atom1.

Definition atoms_conn_returns (atom1: atom_statements)
 (atom2: return_atom_statements) : return_atom_statements :=
   flat_map (fun p1 => 
      map (fun ret_atom =>
          (p1++(fst ret_atom),snd ret_atom)) atom2) atom1.

Definition add_bexp_to_path (s: partial_path_statement) (e:expr) : partial_path_statement :=
  match s with (a, p) =>
    (a, (inl e)::p)
  end.

Inductive AClight_to_Clight : AClight.statement -> Clight.statement -> Prop :=
| to_Clight_assert: forall a,
    AClight_to_Clight (Sassert a) Clight.Sskip
| to_Clight_dummyassert: forall a,
    AClight_to_Clight (Sdummyassert a) Clight.Sskip
| to_Clight_given: forall (A:Type) (HA:Non_empty_Type A) stm c_stm,
    (forall a, AClight_to_Clight (stm a) c_stm) ->
    AClight_to_Clight  (Sgiven A stm) c_stm
| to_Clight_local: forall a1 n a2 stm c_stm,
    AClight_to_Clight  stm c_stm ->
    AClight_to_Clight (Slocal a1 n stm a2) c_stm
| to_Clight_skip:
    AClight_to_Clight AClight.Sskip Clight.Sskip
| to_Clight_assign: forall e1 e2,
    AClight_to_Clight (AClight.Sassign e1 e2) (Clight.Sassign e1 e2)
| to_Clight_set: forall id e,
    AClight_to_Clight (AClight.Sset id e) (Clight.Sset id e)
| to_Clight_builtin: forall id f tlis e,
    AClight_to_Clight (Sbuiltin id f tlis e) (Clight.Sbuiltin id f tlis e)
| to_Clight_call: forall id e elis,
    AClight_to_Clight (AClight.Scall id e elis) (Clight.Scall id e elis)
| to_Clight_sequence: forall stm1 c_stm1 stm2 c_stm2,
    AClight_to_Clight stm1 c_stm1 ->
    AClight_to_Clight stm2 c_stm2 ->
    AClight_to_Clight (Ssequence stm1 stm2) (Clight.Ssequence c_stm1 c_stm2)
| to_Clight_ifthenelse: forall e stm1 c_stm1 stm2 c_stm2,
    AClight_to_Clight stm1 c_stm1 ->
    AClight_to_Clight stm2 c_stm2 ->
    AClight_to_Clight (Sifthenelse e stm1 stm2) (Clight.Sifthenelse e c_stm1 c_stm2)
| to_Clight_loop: forall inv stm1 c_stm1 stm2 c_stm2,
    AClight_to_Clight stm1 c_stm1 ->
    AClight_to_Clight stm2 c_stm2 ->
    AClight_to_Clight (Sloop inv stm1 stm2) (Clight.Sloop c_stm1 c_stm2)
| to_Clight_break:
    AClight_to_Clight AClight.Sbreak Clight.Sbreak
| to_Clight_continue:
    AClight_to_Clight AClight.Scontinue Clight.Scontinue
| to_Clight_return: forall e,
    AClight_to_Clight (AClight.Sreturn e) (Clight.Sreturn e)
| to_Clight_switch: forall e ls c_ls,
    to_Clight_seq ls c_ls ->
    AClight_to_Clight (Sswitch e ls) (Clight.Sswitch e c_ls)
| to_Clight_label: forall id stm c_stm,
    AClight_to_Clight stm c_stm ->
    AClight_to_Clight (Slabel id stm) (Clight.Slabel id c_stm)
| to_Clight_goto: forall id,
    AClight_to_Clight (Sgoto id) (Clight.Sgoto id)

with to_Clight_seq : labeled_statements -> Clight.labeled_statements -> Prop :=
| to_Clight_seq_nil: to_Clight_seq LSnil Clight.LSnil
| to_Clight_seq_cons: 
    forall z stm c_stm seq c_seq,
      AClight_to_Clight stm c_stm ->
      to_Clight_seq seq c_seq ->
      to_Clight_seq (LScons z stm seq)
        (Clight.LScons z c_stm c_seq).


Fixpoint all_basic (pres: list partial_path_statement) :=
  match pres with
  | (Binded_partial _ _  _, _)::_ => false
  | (Basic_partial _, _):: tl => all_basic tl
  | nil => true
  end.

Fixpoint all_empty_path (posts: list partial_path_statement) :=
  match posts with
  | (_, _ :: _)::_ => false
  | (_, nil):: tl => all_empty_path tl
  | nil => true
  end.


Fixpoint all_empty_atom (posts: list path) :=
  match posts with
  | ( _ :: _)::_ => false
  | ( nil):: tl => all_empty_atom tl
  | nil => true
  end.

Definition add_exp_to_pre e (pre:partial_path_statement) :=
  match pre with
  | (a, p) => (a, (inl e)::p)
  end.

Definition add_exp_to_pres e pres :=
  map (add_exp_to_pre e) pres.

Definition add_exp_to_atoms e (atoms:atom_statements) :=
  map (cons (inl e)) atoms.

Definition add_exp_to_return_atom e (ret_atom:return_path_atom):=
  match ret_atom with
  | (p, r) => ((inl e)::p, r)
  end.

Definition add_exp_to_return_atoms e ret_atoms := 
  map (add_exp_to_return_atom e) ret_atoms.



Fixpoint to_Clight  (a: atom_statement) : Clight.statement :=
match a with
| Sskip => Clight.Sskip
| Sassign e1 e2 => Clight.Sassign e1 e2
| Sset id e => Clight.Sset id e
| Scall id e elis => Clight.Scall id e elis
end.

Lemma atoms_conn_pres_nil: forall atoms pres,
  atoms_conn_pres atoms pres = [] <->
  atoms = [] \/ pres = [].
Proof.
  split.
  + induction atoms. 
  - intros. simpl in H. auto.
  - intros. right. destruct pres;auto.
    simpl in *. inversion H.
  + induction atoms;eauto.
    intros. destruct H;eauto.
    - rewrite H. eauto.
    - rewrite H. simpl.
      rewrite H in IHatoms. 
     apply IHatoms.  eauto.
     Qed.

Lemma posts_conn_pres_nil : forall posts pres,
  all_basic posts = true->
  all_basic pres = true->
  posts_conn_pres posts pres = [] <->
  posts = [] \/ pres = [].
Proof.
  intros posts pres E1 E2. split.
  + intros. induction pres.
    - eauto.
    - intros. 
      simpl in H. destruct posts;eauto.
      exfalso. 
      apply app_eq_nil in H.
      destruct H. clear H0.
       destruct a. destruct p. simpl in H. destruct p;auto. destruct p2;auto.
      destruct p0.
      * simpl in H. discriminate H.
      * simpl in H. discriminate H.
      * destruct p0; simpl in H.
        ** discriminate H.
        ** discriminate E2.
      * simpl in H.
        discriminate E1.
  + intros. destruct H;subst;eauto.
    unfold posts_conn_pres. rewrite flat_map_concat_map. unfold posts_conn_pre. induction pres;eauto.   
    simpl. apply IHpres. unfold all_basic in E2. destruct a. destruct p. 
    * destruct pres;eauto.
    * exfalso. discriminate E2.
Qed.    

Lemma atoms_conn_atoms_nil: forall atoms1 atoms2,
  atoms_conn_atoms atoms1 atoms2 = []
  <-> atoms1 = [] \/ atoms2 = [].
Proof.
  intros. split.
  - intros. 
  destruct atoms1;auto.
  right. destruct atoms2;auto.
  inversion H.
  - intros. destruct H. 
  + rewrite H. eauto.
  + rewrite H. induction atoms1;eauto.
Qed.

Lemma atoms_conn_returns_nil: forall atoms1 rets2,
  atoms_conn_returns atoms1 rets2 = []
  <-> atoms1 = [] \/ rets2 = [].
Proof.
  intros. split.
  -
  destruct atoms1;auto.
  right. destruct rets2;auto.
  inversion H.
  - intros. destruct H. 
  + rewrite H.
  destruct rets2;eauto.
  + rewrite H. 
  destruct atoms1;eauto. 
  unfold atoms_conn_returns. 
  rewrite flat_map_concat_map.
  simpl. 
  induction atoms1 ; eauto.
  Qed.
  
  
Lemma posts_conn_basic_pre_cons: forall post posts a2 p2,
  posts_conn_pre (post::posts) (Basic_partial a2, p2) =
  (bind_post_conn_pre post p2 a2) :: posts_conn_pre posts (Basic_partial a2, p2).
Proof.
  intros. destruct post as [a1 p1]. destruct a1; simpl; try auto.
  destruct p1;auto.
Qed.

Lemma posts_conn_pre_app: forall posts1 posts2 pre,
    posts_conn_pre (posts1 ++ posts2) pre =
    posts_conn_pre posts1 pre ++ posts_conn_pre posts2 pre.
Proof.
  intros.
  induction posts1.
  - rewrite app_nil_l. simpl. reflexivity.
  - rewrite <- app_comm_cons.
    destruct a as [a1 p1]. destruct pre0 as [a2 p2].
    destruct a1.
    + destruct p1.
      * destruct a2.
        { simpl.  rewrite IHposts1. reflexivity. }
        { simpl.  rewrite IHposts1. reflexivity. }
      * destruct a2.
        { simpl.  rewrite IHposts1. reflexivity. }
        { simpl.  rewrite IHposts1. reflexivity. }
    + destruct a2; simpl.
      { rewrite IHposts1. auto. }
      { apply IHposts1. }
Qed.

Lemma add_exp_to_atoms_nil: forall a l,  add_exp_to_atoms a l = [] -> l = [].
Proof.
  intros.
  destruct l;auto.
  inv H.
Qed.

Lemma add_exp_to_return_atoms_nil: forall a l,  add_exp_to_return_atoms a l = [] -> l = [].
Proof.
  intros.
  destruct l;auto.
  inv H.
Qed.

Lemma add_exp_to_pres_nil: forall a l,  add_exp_to_pres a l = [] -> l = [].
Proof.
  intros.
  destruct l;auto.
  inv H.
Qed.



Lemma atoms_conn_pres_app1: forall atoms1 atoms2 pres,
    atoms_conn_pres (atoms1 ++ atoms2) pres =
    atoms_conn_pres atoms1 pres ++ atoms_conn_pres atoms2 pres.
Proof.
  intros.
  induction atoms1.
  - rewrite app_nil_l. simpl. reflexivity.
  - rewrite <- app_comm_cons.
    simpl.
    rewrite IHatoms1.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma atoms_conn_pres_nil2: forall atoms,
    atoms_conn_pres atoms [] = [].
Proof.
  intros.
  induction atoms;simpl;auto.
Qed.


Lemma atoms_conn_pres_app2: forall pres1 pres2 atoms x,
  In x (atoms_conn_pres atoms (pres1 ++ pres2)) <->
  In x (atoms_conn_pres atoms pres1  ++ atoms_conn_pres atoms pres2).
Proof.
  intros. induction atoms.
  - simpl. tauto.
  - simpl. split;intro.
    + apply in_or_app. apply in_app_or in H.
      destruct H.
      { rewrite map_app in H. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply in_or_app. auto.
      }
      { apply IHatoms in H. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply in_or_app. auto.
      }
    + apply in_or_app. apply in_app_or in H. destruct H.
      { rewrite map_app. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply IHatoms. apply in_or_app. auto.
      }
      {  rewrite map_app. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply IHatoms. apply in_or_app. auto.
      }
Qed.



Lemma atoms_conn_returns_app1: forall atoms1 atoms2 rets,
    atoms_conn_returns (atoms1 ++ atoms2) rets =
    atoms_conn_returns atoms1 rets ++ atoms_conn_returns atoms2 rets.
Proof.
  intros.
  induction atoms1.
  - rewrite app_nil_l. simpl. reflexivity.
  - rewrite <- app_comm_cons.
    simpl.
    rewrite IHatoms1.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma atoms_conn_returns_app2: forall atoms rets1 rets2 x,
    In x (atoms_conn_returns atoms (rets1++rets2)) <->
    In x (atoms_conn_returns atoms rets1 ++ atoms_conn_returns atoms rets2).
Proof.
  intros.
  induction atoms.
  - rewrite app_nil_l. simpl. reflexivity.
  - split;intro.
    + apply in_or_app. simpl in H.  apply in_app_or in H.
      destruct H.
      { rewrite map_app in H. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply in_or_app. auto.
      }
      { apply IHatoms in H. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply in_or_app. auto.
      }
    + apply in_or_app. apply in_app_or in H. destruct H.
      { rewrite map_app. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply IHatoms. apply in_or_app. auto.
      }
      {  rewrite map_app. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply IHatoms. apply in_or_app. auto.
      }
Qed.