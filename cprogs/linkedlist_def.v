Require Import VST.floyd.proofauto.
From Coq Require Import Psatz.
Require Import cprogs.linkedlist_prog.
Require Import AClight.proofauto.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition t_struct_list := Tstruct _list noattr.

Fixpoint listrep (sigma: list Z) (x: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, 
      data_at Tsh t_struct_list (Vint (Int.repr h),y) x  *  listrep hs y
 | nil => 
    !! (x = nullval) && emp
 end.
Arguments listrep sigma x : simpl never.

Fixpoint lseg (sigma: list Z) (x y: val) : mpred :=
  match sigma with
  | nil => !! (x = y) && emp
  | h::hs => EX u:val, data_at Tsh t_struct_list (Vint (Int.repr h), u) x * lseg hs u y
  end.
Arguments lseg sigma x y : simpl never.

Definition sum_Z (sigma: list Z): Z :=
  fold_right Z.add Z.zero sigma.

Lemma singleton_lseg: forall (a: Z) (x y: val),
  data_at Tsh t_struct_list (Vint (Int.repr a), y) x |-- lseg [a] x y.
Proof.
  intros.
  entailer!. unfold lseg. Exists y. entailer!.
Qed.

Lemma ecancel_singleton_lseg: forall (a: Z) (x y: val),
  data_at Tsh t_struct_list (Vint (Int.repr a), y) x*emp |-- lseg [a] x y.
Proof.
  intros.
  entailer!. unfold lseg. Exists y. entailer!.
Qed.
Lemma ecancel_lseg_singleton: forall (a: Z) (x y: val),
 lseg [a] x y*emp |-- data_at Tsh t_struct_list (Vint (Int.repr a), y) x  .
Proof.
  intros.
  entailer!. unfold lseg. Intros u. subst u. entailer!.
Qed.
Lemma lseg_nullval: forall sigma x,
  lseg sigma x nullval |-- listrep sigma x.
Proof.
  intros.
  revert x; induction sigma; intros.
  + unfold listrep, lseg.
    entailer!.
  + unfold lseg; fold lseg.
    unfold listrep; fold listrep.
    Intros u.
    Exists u.
    sep_apply (IHsigma u).
    entailer!.
Qed.
Lemma ecancel_lseg_nullval: forall sigma x,
  lseg sigma x nullval*emp |-- listrep sigma x.
Proof.
  intros.
  revert x; induction sigma; intros.
  + unfold listrep, lseg.
    entailer!.
  + unfold lseg; fold lseg.
    unfold listrep; fold listrep.
    Intros u.
    Exists u.
    sep_apply (IHsigma u).
    entailer!.
Qed.
Lemma ecancel_nullval_lseg: forall sigma x,
  listrep sigma x*emp |-- lseg sigma x nullval.
Proof.
  intros.
  revert x; induction sigma; intros.
  + unfold listrep, lseg.
    entailer!.
  + unfold lseg; fold lseg.
    unfold listrep; fold listrep.
    Intros u.
    Exists u.
    sep_apply (IHsigma u).
    entailer!.
Qed.
Lemma lseg_lseg: forall (s1 s2: list Z) (x y z: val),
  lseg s1 x y * lseg s2 y z |-- lseg (s1 ++ s2) x z.
Proof.
  intros. generalize dependent x. generalize dependent y.
  generalize dependent z. induction s1.
- simpl. intros. unfold lseg. entailer!. 
- simpl. intros. unfold lseg. entailer!. Exists u.
  entailer!. apply IHs1.
Qed.
Lemma ecancel_lseg_lseg: forall (s1 s2: list Z) (x y z: val),
  lseg s1 x y * lseg s2 y z |-- lseg (s1 ++ s2) x z.
Proof.
  intros. generalize dependent x. generalize dependent y.
  generalize dependent z. induction s1.
- simpl. intros. unfold lseg. entailer!. 
- simpl. intros. unfold lseg. entailer!. Exists u.
  entailer!. apply IHs1.
Qed.
Lemma lseg_list: forall (s1 s2: list Z) (x y: val),
  lseg s1 x y * listrep s2 y |-- listrep (s1 ++ s2) x.
Proof.
  intros. generalize dependent x. generalize dependent y.
  induction s1.
- simpl. intros. unfold lseg. entailer!. 
- simpl. intros. unfold lseg. unfold listrep. entailer!. Exists u.
  entailer!. apply IHs1.
Qed.
Lemma ecancel_lseg_list: forall (s1 s2: list Z) (x y: val),
  lseg s1 x y * listrep s2 y |-- listrep (s1 ++ s2) x.
Proof.
  intros. generalize dependent x. generalize dependent y.
  induction s1.
- simpl. intros. unfold lseg. entailer!. 
- simpl. intros. unfold lseg;fold lseg. unfold listrep;fold listrep. Intros u. Exists u.
    sep_apply IHs1. entailer!.
Qed.

Example lseg_ex: forall s1 s2 s3 x y z,
  lseg s1 x y * lseg s2 y z * lseg s3 z nullval |-- listrep (s1 ++ s2 ++ s3) x.
Proof.
  intros.
  sep_apply (lseg_lseg s2 s3 y z nullval).
  rewrite sepcon_comm.
  sep_apply (lseg_lseg s1 (s2++s3) x y nullval).
  apply lseg_nullval. 
Qed.

Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).
Proof.
intros.
revert p. induction sigma; 
  unfold listrep; fold listrep; intros; normalize.
apply prop_right; split; simpl; auto. intuition.
entailer!.
split; intro. subst p. destruct H; contradiction. inv H2.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
 destruct sigma; unfold listrep; fold listrep;
 intros; normalize.
 auto with valid_pointer.
 apply sepcon_valid_pointer1.
 apply data_at_valid_ptr; auto.
 simpl;  computable.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Lemma sum_Z_snoc:
  forall a b, sum_Z (a++b :: nil) = Z.add (sum_Z a) b.
Proof.
  intros. unfold sum_Z. induction a.
- simpl. omega.
- simpl. rewrite IHa. omega. 
Qed.

Lemma lemmaforappend: forall s3 y0 i0 y1 p,lseg s3 y0 p * data_at Tsh t_struct_list (Vint (Int.repr i0), y1) p
|-- lseg (s3 ++ [i0]) y0 y1.
Proof.
  induction s3.
  - intros. rewrite app_nil_l. unfold lseg. Exists y1.
  entailer!.
  - intros. assert((a :: s3) ++ [i0]=(a :: (s3 ++ [i0]))).
  { auto. } rewrite H. unfold lseg. entailer!. fold lseg.
  Exists u. entailer!. apply IHs3.
Qed.

Fixpoint lbseg (sigma: list Z) (x y: val) : mpred :=
  match sigma with
  | nil => !! (x = y) && emp
  | h::hs => EX u:val, data_at Tsh (tptr t_struct_list) u x *
            field_at Tsh t_struct_list [StructField _head] (Vint (Int.repr h)) u *
            lbseg hs (field_address t_struct_list [StructField _tail]  u) y
  end.

Lemma tmp:forall s3 x s y,
lbseg s3 x s*data_at Tsh (tptr t_struct_list) y s
|--EX  u, data_at Tsh (tptr t_struct_list) u x*lseg s3 u y.
Proof.
   induction s3;intros.
   + Exists y. unfold lbseg;unfold lseg. entailer!.
   + unfold lbseg;fold lbseg. Intros u. Exists u. entailer!.
   unfold lseg;fold lseg. sep_apply IHs3. Intros u0.
   Exists u0. entailer!.
   unfold_data_at (data_at Tsh t_struct_list _ u). entailer!.
Qed.
Lemma tmp2:forall s3 u x t i, data_at Tsh (tptr t_struct_list) u x * lseg s3 u t *
field_at Tsh t_struct_list [StructField _head] (Vint (Int.repr i)) t
|-- lbseg (s3 ++ [i]) x (field_address t_struct_list [StructField _tail] t).
Proof.
 induction s3.
  -- intros. unfold lseg at 1. Intros. rewrite H. rewrite app_nil_l.
  unfold lbseg. Exists t. entailer!.
  -- intros. unfold lseg at 1;fold lseg. Intros u0. simpl. Exists u.
  entailer!. unfold_data_at (data_at Tsh t_struct_list _ u).
  assert(
field_at Tsh t_struct_list [StructField _tail] u0 u 
|--data_at Tsh (tptr t_struct_list) u0 (field_address t_struct_list [StructField _tail] u)).
{ entailer!. }
 sep_apply H5. sep_apply IHs3. entailer!.
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
(***************************************************************
 *                                                             *
 *                                                             *
 *                  This is for automation                     *
 *                                                             *
 *                                                             *
 *                                                             *
 ***************************************************************)
Lemma ecancel_list: forall p l,
  listrep l p * emp |-- listrep l p.
Proof.
  intros.
  rewrite sepcon_emp; auto.
Qed.

Lemma ecancel_lseg: forall p q l,
  lseg l p q* emp |-- lseg l p q.
Proof.
  intros.
  rewrite sepcon_emp; auto.
Qed.
Lemma ecancel_nil_listrep: forall p ,
  p = nullval ->
  emp |-- listrep nil p.
Proof.
  intros.
  subst; unfold listrep.
  entailer!.
Qed.
Lemma ecancel_nil_lseg: forall p q,
  p = q ->
  emp |-- lseg nil p q.
Proof.
  intros.
  subst; unfold lseg.
  entailer!.
Qed.
Lemma ecancel_sole_lseg: forall (p q : val) (x:Z),
  data_at Tsh t_struct_list (Vint(Int.repr x), q) p  |-- lseg [x] p q.
Proof.
  intros.
  unfold lseg.
  Exists q.
  entailer!.
Qed.
Lemma ecancel_head: forall (p q : val) (x:Z) (l:list Z),
  data_at Tsh t_struct_list (Vint(Int.repr x), q) p * listrep l q |-- listrep (x :: l) p.
Proof.
  intros.
  unfold listrep at 2; fold listrep.
  Exists q.
  entailer!.
Qed.

Lemma ecancel_cell: forall p xq,
  data_at Tsh t_struct_list xq p * emp |-- data_at Tsh t_struct_list xq p.
Proof.
  intros.
  rewrite sepcon_emp; auto.
Qed.

Ltac solve_eq:=
idtac;
match goal with
| |- ?x = ?x => apply eq_refl
| |- ?x = ?u =>first [is_evar x;apply eq_refl|
first [is_evar u;apply eq_refl|auto]] end.

Lemma same_data_at_l_r: forall sh (p:val) (q:val) (x:val) (x':val) (q':val),x=x'->q=q'->
   data_at sh t_struct_list (x, q) p * emp |--
       data_at sh t_struct_list (x', q') p .
Proof.
  intros. rewrite sepcon_emp. entailer!.
Qed.

Lemma ecancel_nullval_listrep: forall l ,
  l = nil ->
  emp |-- listrep l nullval.
Proof.
  intros.
  subst; unfold listrep.
  entailer!.
Qed.
Lemma ecancel_same_lseg: forall l p,
  l = nil ->
  emp |-- lseg l p p.
Proof.
  intros.
  subst; unfold lseg.
  entailer!.
Qed.
Lemma ecancel_nullval_lseg': forall sigma x sigma',sigma=sigma'->
  listrep sigma x*emp  |-- lseg sigma' x nullval.
Proof.
  intros. subst.
  revert x; induction sigma'; intros.
  + unfold listrep, lseg.
    entailer!.
  + unfold lseg; fold lseg.
    unfold listrep; fold listrep.
    Intros u.
    Exists u.
    sep_apply (IHsigma' u).
    entailer!.
Qed.
Lemma ecancel_lseg_nullval': forall sigma x sigma',sigma=sigma'->
  lseg sigma x nullval*emp|--listrep sigma' x  .
Proof.
  intros. subst.
  revert x; induction sigma'; intros.
  + unfold listrep, lseg.
    entailer!.
  + unfold lseg; fold lseg.
    unfold listrep; fold listrep.
    Intros u.
    Exists u.
    sep_apply (IHsigma' u).
    entailer!.
Qed.
Lemma ecancel_lseg_data_at: forall z y t p s1 s2,s1++[z]=s2->
data_at Tsh t_struct_list (Vint (Int.repr z), y) t* lseg s1 p t
|--lseg s2 p y.
Proof.
  intros. sep_apply singleton_lseg. sep_apply (lseg_lseg s1 [z] p t y).
  subst. auto.
Qed.
Lemma ecancel_lseg_data_at': forall z y t p s1 s2,z::s1=s2->
data_at Tsh t_struct_list (Vint (Int.repr z), t) p* lseg s1 t y
|--lseg s2 p y.
Proof.
  intros. sep_apply singleton_lseg. sep_apply (lseg_lseg  [z] s1 p t y).
  subst. simpl. auto.
Qed.
 

Lemma ecancel_lseg_listrep: forall s1 s2 p q,lseg s1 p q*listrep s2 q |-- listrep (s1++s2) p.
Proof.
  intros. apply lseg_list.
Qed.
Lemma ecancel_lseg_listrep': forall s1 s2 s3 p q,s1++s2=s3->lseg s1 p q*listrep s2 q |-- listrep s3 p.
Proof.
  intros. subst. apply lseg_list.
Qed.
Lemma ecancel_listrep_data_at: forall z t p s1 s2,z::s1=s2->
data_at Tsh t_struct_list (Vint (Int.repr z), t) p* listrep s1 t
|--listrep s2 p.
Proof.
  intros. sep_apply singleton_lseg.
   sep_apply (lseg_list  [z] s1 p t ).
  subst. simpl. auto.
Qed.
Lemma ecancel_nil_lbseg: forall l p,
  l = nil ->
  emp |-- lbseg l p p.
Proof.
  intros.
  subst; unfold lbseg.
  entailer!.
Qed.
Lemma ecancel_listrep_nullval: forall l,
  l = nil ->
  emp |-- listrep l nullval.
Proof.
  intros.
  subst; unfold listrep.
  entailer!.
Qed.
Lemma ecancel_samelistrep: forall p l u,
  l = u ->
  listrep l p*emp |-- listrep u p.
Proof.
  intros.
  subst.
  entailer!.
Qed.
Lemma ecancel_samelseg: forall p q l u,
  l = u ->
  lseg l p q*emp |-- lseg u p q.
Proof.
  intros.
  subst.
  entailer!.
Qed.
Lemma ecancel_data_at_ptpr: forall p x,
  data_at Tsh (tptr t_struct_list) p x*emp  |-- data_at Tsh (tptr t_struct_list) p x.
Proof.
  entailer!.
Qed.
Lemma ecancel_data_at_ptpr': forall p q x,p=q->
  data_at Tsh (tptr t_struct_list) p x*emp  |-- data_at Tsh (tptr t_struct_list) q x.
Proof.
  entailer!.
Qed.
Lemma ecancel_lbseg: forall l p q,
  lbseg l p q*emp  |-- lbseg l p q.
Proof.
  entailer!.
Qed.
Lemma ecancel_samelbseg: forall l l' p q,l=l'->
  lbseg l p q*emp  |-- lbseg l' p q.
Proof.
intros.
subst.
  entailer!.
Qed.

Lemma ecancel_head': forall (p q : val) (x:Z) (l:list Z)(l':list Z),x :: l=l'->
  data_at Tsh t_struct_list (Vint(Int.repr x), q) p * listrep l q |-- listrep l' p.
Proof.
  intros. subst.
  unfold listrep at 2; fold listrep.
  Exists q.
  entailer!.
Qed.

Lemma ecancel_lbsegtail: forall l p q q',q=q'->
  lbseg l p q*emp  |-- lbseg l p q'.
Proof.
intros.
subst.
  entailer!.
Qed.

Lemma ecancel_lbseg_lbseg:forall  l p q u z,
lbseg l p q*(data_at Tsh (tptr t_struct_list) u q*field_at Tsh t_struct_list [StructField _head] (Vint (Int.repr z)) u)
|-- lbseg (l++[z]) p (field_address t_struct_list [StructField _tail] u).
Proof.
  induction l.
  + intros. rewrite app_nil_l. unfold lbseg. entailer!. Exists u. entailer!.
  + intros. simpl. Intros u0. Exists u0. entailer!. sep_apply IHl. entailer!.
Qed.
Lemma ecancel_lbseg_lbseg':forall  l p q u z a,a=l++[z]->
lbseg l p q*(data_at Tsh (tptr t_struct_list) u q*field_at Tsh t_struct_list [StructField _head] (Vint (Int.repr z)) u)
|-- lbseg a p (field_address t_struct_list [StructField _tail] u).
Proof.
  intros. subst a. apply ecancel_lbseg_lbseg.
Qed.
Lemma cancel_field_at_head:forall x t P,field_at Tsh t_struct_list [StructField _head] (Vint (Int.repr x)) t*P |--(P*field_at Tsh t_struct_list [StructField _head] (Vint (Int.repr x)) t).
Proof.
  intros;entailer!.
Qed.
Lemma cancel_field_at_head':forall x u t P,x=u->field_at Tsh t_struct_list [StructField _head] (Vint (Int.repr x)) t*P |--(P*field_at Tsh t_struct_list [StructField _head] (Vint (Int.repr u)) t).
Proof.
  intros. subst;entailer!.
Qed.
Ltac local_list_cancel :=
  idtac;
  match goal with
  | |- _ |-- listrep ?l nullval =>refine(ecancel_listrep_nullval l _);solve [auto]
  | |- _ |-- lseg ?l ?x ?x =>refine(ecancel_same_lseg l x _);solve [auto]
  | |- _ |-- lbseg ?l ?x ?x =>refine(ecancel_nil_lbseg l x _);solve [auto]
  | |- lbseg ?l ?p ?q*_ |-- lbseg (?p++[?z]) ?p (field_address t_struct_list [StructField _tail] ?u) =>exact (ecancel_lbseg_lbseg l p q u z)
  | |- lbseg ?l ?p ?q*_ |-- lbseg ?a ?p (field_address t_struct_list [StructField _tail] ?u) =>first[is_evar a;refine (ecancel_lbseg_lbseg l p q u _ ) |refine (ecancel_lbseg_lbseg' l p q u _ a _)]
  | |- field_at Tsh t_struct_list [StructField _head] (Vint (Int.repr ?x)) ?t*_ |--
  (_ * field_at Tsh t_struct_list [StructField _head] (Vint (Int.repr ?u)) ?t) =>
  first[is_evar u;refine (cancel_field_at_head x t _)|refine (cancel_field_at_head' x u t _ _)]
  | |- data_at Tsh (tptr t_struct_list) ?p ?x*_ |-- data_at Tsh (tptr t_struct_list) ?q ?x=>
first [is_evar q;exact(ecancel_data_at_ptpr p x)|refine(ecancel_data_at_ptpr' p q x _);try solve [auto]]
  | |- lbseg ?l ?p ?q*_ |-- lbseg ?u ?p ?q=>
first[is_evar u;exact(ecancel_lbseg l p q)|refine (ecancel_samelbseg l u p q _);solve [auto]]
  | |- lbseg ?l ?p ?q*_ |-- lbseg ?l ?p ?u=>
first[is_evar u;exact(ecancel_lbseg l p q)|refine (ecancel_lbsegtail l u p q _);solve [auto]]
  | |- data_at ?sh t_struct_list (?x, ?q) ?p * _ |--
       data_at ?sh t_struct_list (?u, ?v) ?p =>
       refine (same_data_at_l_r sh p q x u v _ _) ;[solve_eq|solve_eq]
  | |- emp |-- listrep nil ?p =>
         refine (ecancel_nil_listrep p _); solve [auto]
  | |- emp |-- listrep ?l (Vint(Int.repr 0)) =>
         refine (ecancel_nullval_listrep nil _); solve [auto]
  | |- emp |-- listrep ?l nullval =>
         refine (ecancel_nullval_listrep nil _); solve [auto] 
  | |- emp |-- lseg nil ?p ?q=>
         refine (ecancel_nil_lseg p q _); solve_eq
  | |- data_at ?sh t_struct_list (?x, ?q) ?p * _ |--
       listrep ?sh _ ?p =>
         refine (ecancel_head' sh p q x _)
  | |- listrep ?l ?p * _ |--
       listrep  ?u ?p =>
        first[is_evar u;exact (ecancel_list p l)|refine (ecancel_samelistrep p l u _);try solve [auto] ]
  | |- lseg ?l ?p ?q* _ |--
       lseg  ?u ?p ?q=>
          first[is_evar u;exact (ecancel_list p q l)|refine (ecancel_samelseg p q l u _); solve [auto] ]
  | |- data_at Tsh t_struct_list (Vint(Int.repr ?x), ?q) ?p * _ |--
       listrep (?x :: ?l) _ =>
         exact (ecancel_head  p q x l)
  | |- data_at Tsh  t_struct_list (Vint(Int.repr ?x), ?q) ?p * _ |--
       listrep  ?u ?p =>
         first[is_evar u;refine (ecancel_head  p q x _)|refine (ecancel_head' p q x _ u _)]
  | |- lseg [?a] ?x ?y*_ |--
       data_at Tsh t_struct_list (Vint (Int.repr ?a), ?y) ?x=>
       exact(ecancel_lseg_singleton a x y)
  | |- data_at Tsh t_struct_list (Vint (Int.repr ?a), ?y) ?x*_ |--
       lseg _ ?x ?y=>
       exact(ecancel_singleton_lseg a x y)
  | |- lseg ?x ?y nullval*_ |--
       listrep ?x ?y=>
       exact(ecancel_lseg_nullval x y)
  | |- lseg ?x ?y nullval* _ |--
       listrep ?u ?y=>
       refine(ecancel_lseg_nullval' x y u _)
  | |- listrep ?x ?y*_ |--
       lseg ?x ?y nullval=>
       exact(ecancel_nullval_lseg x y)
  | |- listrep ?x ?y*_ |--
       lseg ?u ?y nullval=>
       refine(ecancel_nullval_lseg' x y u _)
  | |- lseg ?s1 ?p ?q*_ |--listrep (?s1++?s2) ?p =>
  refine(ecancel_lseg_listrep s1 _ p q)
  | |- lseg ?s1 ?p ?q*_ |--listrep ?s2 ?p=>
  first[is_evar s2;refine(ecancel_lseg_listrep s1 _ _ p q) |refine (ecancel_lseg_listrep' s1 _ s2 p q _)]
  | |- lseg ?s1 ?x ?y *_|-- lseg (?s1 ++ ?s2) ?x ?z =>
       exact (ecancel_lseg_lseg s1 s2 x y z)
  | |- lseg ?s2 ?y ?z * _ |-- lseg (?s1 ++ ?s2) ?x ?z =>
       exact (ecancel_lseg_lseg s1 s2 x y z)
  | |- lseg ?s1 ?x ?y * _ |-- lseg _ ?x ?z =>
       refine (ecancel_lseg_lseg s1 _ x y z)
  | |- lseg ?s2 ?y ?z * _ |-- lseg _ ?x ?z =>
       refine (ecancel_lseg_lseg _ s2 x y z)
  end.


Lemma listrep_unify: forall p l1 l2,
  l1 = l2 ->
  listrep l1 p |-- listrep l2 p.
Proof.
  intros.
  subst.
  auto.
Qed.

Lemma lseg_unify: forall p q l1 l2,
  l1 = l2 ->
  lseg l1  p q |-- lseg l2 p q.
Proof.
  intros.
  subst.
  auto.
Qed.
Ltac global_listrep_cancel :=
  idtac;
  match goal with
  | |- listrep ?l1 ?p |--
       listrep ?l2 _ =>
         refine (listrep_unify p l1 l2 _)
  end.
Ltac global_lseg_cancel :=
  idtac;
  match goal with
  | |- lseg ?l1 ?p ?q|--
       lseg ?l2 _ _=>
         refine (listrep_unify p q l1 l2 _)
  end.
Ltac list_cancel :=
  eapply symbolic_cancel_setup;
  [ construct_fold_right_sepcon
  | construct_fold_right_sepcon
  | fold_abnormal_mpred
  | cbv iota beta delta [before_symbol_cancel];
    conservative_syntactic_cancel
      local_list_cancel;
    match goal with
       | |- _ |-- _ =>
      first [ simple apply syntactic_cancel_solve3
          | match goal with
            | |- fold_right_sepcon ?A |-- fold_right_sepcon ?B => rewrite <- (fold_left_sepconx_eq A), <- (fold_left_sepconx_eq B)
            end;
            unfold fold_left_sepconx; cbv iota beta;
            first
            [ simple apply derives_refl
            | global_listrep_cancel ] ]
        | _ =>idtac end    ].

Lemma listrep_is_null: forall l p,
  p = nullval ->
  listrep l p |-- !! (p = nullval /\ l = nil) && emp.
Proof.
  intros.
  saturate_local.
  assert (l = nil) by tauto.
  entailer!.
  unfold listrep.
  entailer!.
Qed.
Lemma listrep_isptr: forall l p,
  isptr p ->
  listrep l p |--
    EX x l' q, !! (l = x :: l') &&
      data_at Tsh t_struct_list (Vint(Int.repr x), q) p *
      listrep l' q.
Proof.
  intros.
  saturate_local.
  destruct l; [pose proof proj2 H0 eq_refl; subst; tauto |].
  clear H0 PNp.
  Exists z l.
  unfold listrep at 1; fold listrep.
  Intros t; Exists t.
  entailer!.
Qed.

Lemma listrep_not_nullval:
forall (l : list Z) (p : val),
       p<>nullval ->
       listrep l p
       |-- EX (x : Z) (l' : list Z) (q : val),
           !! (l = x :: l') &&
           data_at Tsh t_struct_list (Vint (Int.repr x), q) p *
           listrep l' q.
Proof.
  intros. destruct l.
  + unfold listrep. Intros. destruct H;auto.
  + unfold listrep;fold listrep. Intros y. Exists z l y. entailer.
Qed.
Ltac pre_process :=
  repeat match goal with
  | H: ?t=nullval |- _ =>subst t end ;
  let RHS := fresh "RHS" in 
  match goal with
  | |- _ |-- ?P => set (RHS := P)
  end;
  repeat
  match goal with
  | H: isptr ?p |- context [listrep ?l ?p] =>
         sep_apply (listrep_isptr l p);
         let x := fresh "x" in
         let ll := fresh "l" in
         let pp := fresh "p" in
         Intros x ll pp
  | H: ?x <> nullval |- context [listrep ?l ?p] =>
         sep_apply (listrep_not_nullval l p);
         let x := fresh "x" in
         let ll := fresh "l" in
         let pp := fresh "p" in
         Intros x ll pp
  | H: ?p = nullval |- context [listrep ?l ?p] =>
         sep_apply (listrep_is_null l p);
         Intros
  | |- context [listrep ?l nullval] =>
         sep_apply (listrep_is_null l nullval);
         Intros
  end;
  subst RHS.
Ltac unify_for_go_lower ::=
    match goal with |- fold_right_PROP_SEP (VST_floyd_app ?A ?B) ?C = _ =>
      repeat match B with context [(?x = ?y) :: _] =>
       is_evar x; progress (unify x y)
      end
    end.    
Ltac unify_for_already_lower :=
  idtac;
  match goal with
  | |- _ |--  andp (prop ?A) _ =>
        repeat
         match A with
         | context [ (?x = ?y) /\ _ ] => has_evar y; progress unify x y
         | (?x = ?y) => has_evar y; progress unify x y
         end
  | _ => idtac
  end.
Ltac list_entailer :=
  Intros;
  pre_process;
  match goal with
  | |- ENTAIL _, PROPx _ (LOCALx _ (SEPx _)) |-- _ =>
         repeat EExists; go_lower
  | |- @derives mpred _ _ _ =>
         repeat EExists; unify_for_already_lower
  end;
  saturate_local;
  first [ apply andp_right; [apply prop_right | try list_cancel];
          [repeat split; auto | ..]
        | try list_cancel].
        
