Require Import VST.floyd.proofauto.
From Coq Require Import Psatz.
Require Import cprogs.dlinklist_prog.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition t_struct_list := Tstruct _list noattr.

Fixpoint listrep_pre (sigma: list Z) (x: val) (t:val): mpred :=
 match sigma with
 | nil => 
    !! (x = nullval)&& emp
 | h::hs => 
    EX y:val, 
      data_at Tsh t_struct_list (Vint (Int.repr h),(y,t)) x  *  listrep_pre hs y x
 end.
Definition listrep (sigma: list Z) (x: val) : mpred :=
listrep_pre sigma x nullval.
Arguments listrep sigma x : simpl never.

Fixpoint lseg_pre (sigma: list Z) (x y: val)(t s:val) : mpred :=
  match sigma with
  | nil => !! (x = y) &&!! (t = s)&& emp
  | h::hs => EX u:val, data_at Tsh t_struct_list (Vint (Int.repr h) , (u,t)) x * lseg_pre hs u y x s
  end.
  
Definition lseg (sigma: list Z) (x y: val) : mpred := EX t:val,
lseg_pre sigma x y nullval t.
Arguments lseg sigma x : simpl never. 

Definition sum_Z (sigma: list Z): Z :=
  fold_right Z.add Z.zero sigma.

Lemma listrep_local_facts:
  forall sigma p q,
   listrep_pre sigma p q |--
   !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).
Proof.
induction sigma.
+ intros. unfold listrep. unfold listrep_pre. entailer!.
split. intros. auto. intros. auto.
+ intros. unfold listrep. unfold listrep_pre;fold listrep_pre. Intros y.
entailer!.
split; intro. subst p. destruct H; contradiction. inv H2.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p q,
   listrep_pre sigma p q|-- valid_pointer p.
Proof.
 destruct sigma; unfold listrep;unfold listrep_pre; fold listrep_pre;
 intros; normalize.
 auto with valid_pointer.
 apply sepcon_valid_pointer1.
 apply data_at_valid_ptr; auto.
 simpl;  computable.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Lemma singleton_lseg: forall (a: Z) (x y z: val),
  data_at Tsh t_struct_list (Vint (Int.repr a), (y,z)) x |-- lseg_pre [a] x y z x .
Proof.
  intros. unfold lseg_pre. Exists y.
  entailer!.
Qed.

Lemma lseg_nullval_pre: forall sigma x y z,
  lseg_pre sigma x nullval y z|-- listrep_pre sigma x y.
Proof.
  intros.
  revert x y z; induction sigma; intros.
  + unfold listrep_pre;unfold lseg_pre.
    entailer!.
  + unfold lseg_pre;unfold listrep_pre.
    fold lseg_pre; fold listrep_pre.
    Intros u.
    Exists u. entailer!.
Qed.

Lemma lseg_nullval: forall sigma x,
  lseg sigma x nullval|-- listrep sigma x.
Proof.
  intros.
  unfold lseg. Intros t. apply lseg_nullval_pre.
Qed.

Lemma lseg_lseg_pre: forall (s1 s2: list Z) (x y z w u v: val),
  lseg_pre s1 x y w u* lseg_pre s2 y z u v|-- lseg_pre (s1 ++ s2) x z w v.
Proof.
  intros. revert x y z w u v. induction s1.
- simpl. intros. unfold lseg_pre;fold lseg_pre. entailer!. 
- simpl. intros. Intros u0. Exists u0. unfold lseg. unfold lseg_pre;fold lseg_pre. entailer!. 
  entailer!. 
Qed.
Lemma lseg_listrep_pre :forall s1 p s t,lseg_pre s1 p nullval t s |-- listrep_pre s1 p t.
Proof.
  induction s1.
  - intros. simpl. entailer!.
  - intros. simpl. Intros u. Exists u.
  entailer!.
Qed.
Lemma sum_Z_snoc:
  forall a b, sum_Z (a++b :: nil) = Z.add (sum_Z a) b.
Proof.
  intros. unfold sum_Z. induction a.
- simpl. omega.
- simpl. rewrite IHa. omega. 
Qed.


Fixpoint min_Z (sigma: list Z): Z :=
match sigma with
|nil => Int.max_unsigned
|h::t =>Z.min h (min_Z t)
end.

Fixpoint max_Z (sigma: list Z): Z :=
match sigma with
|nil => Z.zero
|h::t =>Z.max h (max_Z t)
end.
Lemma zero_le:0 <= Z.zero <= Int.max_unsigned.
Proof.
  split.
  + apply Z.le_refl.
  + apply Z.le_trans with  (Int.unsigned Int.zero). 
  apply  Int.unsigned_range_2. apply  Int.unsigned_range_2.
Qed.
Lemma umax_le:0 <= Int.max_unsigned <= Int.max_unsigned.
Proof.
  split.
  + apply Z.le_trans with  (Int.unsigned Int.zero). 
  apply  Int.unsigned_range_2. apply  Int.unsigned_range_2.
  + apply Z.le_refl.
Qed.

Lemma max_min1:forall s,s<>nil->min_Z s<=max_Z s.
Proof.
  induction s.
  + intros. destruct H. auto. 
  + intros. unfold min_Z;unfold max_Z;fold min_Z;fold max_Z. 
  apply Z.le_trans with a.
  ++ apply Z.le_min_l.
  ++ apply Z.le_max_l.
Qed.
Lemma max_min2:forall s1 z,max_Z (s1 ++ [z])=Z.max(max_Z s1) z.
Proof.
  induction s1.
  + intros. rewrite app_nil_l. unfold max_Z. apply computable_theorems.Zmax_comm.
  + intros. assert((a :: s1) ++ [z]=a :: (s1 ++ [z])).
  { simpl. auto. } rewrite H. unfold max_Z;fold max_Z.
  rewrite IHs1. apply Z.max_assoc.
Qed.
Lemma max_min3:forall s1 z,min_Z (s1 ++ [z])=Z.min(min_Z s1) z.
Proof.
  induction s1.
  + intros. rewrite app_nil_l. unfold min_Z. apply Z.min_comm.
  + intros. assert((a :: s1) ++ [z]=a :: (s1 ++ [z])).
  { simpl. auto. } rewrite H. unfold min_Z;fold min_Z.
  rewrite IHs1. apply Z.min_assoc.
Qed.
Lemma max_min4:forall s1 z s2,z<=max_Z (s1++[z]++s2).
Proof.
  induction s1.
  - intros. rewrite app_nil_l. simpl. apply Z.le_max_l.
  - simpl. intros. apply Z.le_trans with (max_Z (s1 ++ [z] ++ s2)). auto. apply Z.le_max_r.
Qed.
Lemma max_min5:forall s1 z s2,min_Z (s1++[z]++s2)<=z.
Proof.
  induction s1.
  - intros. rewrite app_nil_l. simpl. apply Z.le_min_l.
  - simpl. intros. apply Z.le_trans with (min_Z (s1 ++ [z] ++ s2)). apply Z.le_min_r. apply IHs1.
Qed.
Lemma max_min6_pre:forall s,Z.zero<=max_Z s.
Proof.
  intros.
  induction s.
  - simpl. omega.
  - unfold max_Z;fold max_Z. apply Z.le_trans with (max_Z s).
  auto. apply Z.le_max_r.
Qed.
Lemma max_min6:forall s1 z s2,max_Z s1<=max_Z (s1++[z]++s2).
Proof.
  intros. induction s1.
- simpl. apply Z.le_trans with (max_Z s2). apply max_min6_pre. apply Z.le_max_r.
- simpl. apply Z.max_le_compat_l. auto.
Qed.
Lemma max_min7_pre:forall s,min_Z s<=Int.max_unsigned.
Proof.
  intros.
  induction s.
  - simpl. omega.
  - unfold min_Z;fold min_Z. apply Z.le_trans with (min_Z s).
  auto. apply Z.le_min_r. auto.
Qed.
Lemma max_min7:forall s1 z s2,min_Z (s1++[z]++s2)<=min_Z s1.
Proof.
  intros. induction s1.
- simpl. apply Z.le_trans with (min_Z s2). apply Z.le_min_r. apply max_min7_pre.
- simpl. apply Z.min_le_compat_l. auto.
Qed.

Lemma lemmaforappend:forall s1 p t s z y r,
lseg_pre s1 p t r s * data_at Tsh t_struct_list (Vint (Int.repr z), (y, s)) t
|-- lseg_pre (s1 ++ [z]) p y r t.
Proof.
  simpl. intros. sep_apply (singleton_lseg z t y s).
  sep_apply (lseg_lseg_pre s1 [z] p t y r s t). entailer!.
Qed.


Lemma lseg_listrep_app:forall s1 s2 a b c d,
lseg_pre s1 a b c d*listrep_pre s2 b d |--listrep_pre (s1++s2) a c.
Proof.
  induction s1.
  + intros. unfold lseg_pre at 1.  simpl. entailer!.
  + intros. unfold lseg_pre;fold lseg_pre.
  Intros u. simpl. Exists u. entailer!. apply IHs1.
Qed.




Lemma temmp:forall sigma a u v q  p t,
data_at Tsh t_struct_list (Vint (Int.repr a), (u, v)) q * lseg_pre sigma u p q t
|-- !! is_pointer_or_null t.
Proof.
simpl. induction sigma.
+ intros. unfold lseg_pre. Intros. subst q. entailer!.
+ intros. unfold lseg_pre;fold lseg_pre. Intros u0.
sep_apply (IHsigma a u0 q u p t). entailer!.
Qed.
Lemma lsegpre_local_facts':
  forall sigma p q t,
   lseg_pre sigma q p nullval t|-- !! is_pointer_or_null t.
Proof.
 induction sigma; unfold lseg_pre;unfold lseg_pre; fold lseg_pre;
 intros. 
 - entailer!.
 - Intros u.
  apply temmp.
Qed.  

Hint Resolve lsegpre_local_facts' : saturate_local.
(* Definition Delete_spec :=
 DECLARE _Delete
  WITH s1 : list Z,s2:list Z, p: val, q:val, t:val,z:Z,r:val
  PRE  [ _p OF (tptr t_struct_list),_q OF (tptr t_struct_list) ]
     PROP ()
     LOCAL (temp _p p;temp _q q)
     SEP (lseg_pre s1 p q nullval t;lseg_pre [z] q r t q;listrep_pre s2 r q)
  POST [ (tptr t_struct_list) ]
     PROP () 
     LOCAL (temp ret_temp p)
     SEP (lseg_pre s1 q p nullval t;listrep_pre s2 p t).
     
Lemma body_Delete: semax_body Vprog Gprog f_Delete Delete_spec.
Proof.
start_function. forward_if (
     PROP () 
     LOCAL (temp ret_temp p)
     SEP (lseg_pre s1 q p nullval t;listrep_pre s2 p t)).
  + admit.
  + forward_if (
     PROP () 
     LOCAL (temp ret_temp p)
     SEP (lseg_pre s1 q p nullval t;listrep_pre s2 p t)).
  ++ destruct s1.
  +++ unfold lseg_pre. Intros u. entailer!.
  +++ unfold lseg_pre;fold lseg_pre. Intros u. Intros u0. entailer!.
  ++ simpl. Intros u. destruct s1.
  +++ unfold lseg_pre. Intros. admit.
  +++ unfold lseg_pre;fold lseg_pre. Intros u0. forward.
  ++++ entailer!. admit.
  ++++ admit.
Admitted. *)
