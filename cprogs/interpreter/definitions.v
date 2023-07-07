Require Import Lia.
Require Import FloydSeq.precise_lemmas.
Require Import FloydSeq.precise_proofauto.
Require Import utils.VSTALib.
Require Import cprogs.interpreter.program.
Local Open Scope logic.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Notation "'IntRepr'" := (Int.repr).
Notation "'store_int' p x" :=
  (@data_at CompSpecs Tsh tint (Vint(IntRepr(x))) p)
  (x at level 0, p at level 0, at level 0).

Notation "'store_expr' p t v n op arg1 arg2" :=
  (@data_at CompSpecs Tsh (Tstruct _expr noattr)
    (@pair val (val * (val * (val * (val * val)))) (Vint(IntRepr(t)))
      (@pair val (val * (val * (val * val))) (Vint(IntRepr(v)))
        (@pair val (val * (val * val)) n
          (@pair val (val * val) (Vint(IntRepr(op)))
            (@pair val val arg1 arg2)))))
    p)
  ( t at level 0, v at level 0, n at level 0, op at level 0
  , arg1 at level 0, arg2 at level 0, p at level 0, at level 0).
Notation "'store_expr_' p" :=
  (@data_at_ CompSpecs Tsh (Tstruct _expr noattr) p)
  (p at level 0, at level 0).

Notation "'store_cmd' p t n arg1 arg2 sub1 sub2" :=
  (@data_at CompSpecs Tsh (Tstruct _cmd noattr)
    (@pair val (val * (val * (val * (val * val)))) (Vint(IntRepr(t)))
      (@pair val (val * (val * (val * val))) n
        (@pair val (val * (val * val)) arg1
          (@pair val (val * val) arg2
            (@pair val val sub1 sub2)))))
    p)
  ( t at level 0, n at level 0, arg1 at level 0, arg2 at level 0
  , sub1 at level 0, sub2 at level 0, p at level 0, at level 0).
Notation "'store_cmd_' p" :=
  (@data_at_ CompSpecs Tsh (Tstruct _cmd noattr) p)
  (p at level 0, at level 0).

Notation "'store_cont_list' p c link" :=
  (@data_at CompSpecs Tsh (Tstruct _cont_list noattr) (@pair val val c link) p)
  (c at level 0, link at level 0, p at level 0, at level 0).
Notation "'store_cont_list_' p" :=
  (@data_at_ CompSpecs Tsh (Tstruct _cont_list noattr) p)
  (p at level 0, at level 0).

Notation "'store_res_prog' p foc ectx" :=
  (@data_at CompSpecs Tsh (Tstruct _res_prog noattr) (@pair val val foc ectx) p)
  (foc at level 0, ectx at level 0, p at level 0, at level 0).

Notation "'tc_val_uint'" := (tc_val tuint).

Parameter memory_rep : val -> mpred.
Parameter hash_table_rep : val -> mpred.

Inductive binop :=
  | O_Plus | O_Minus | O_Mul | O_Div | O_Mod
  | O_Lt | O_Eq
  | O_And | O_Or.

Definition enum_of_binop (op : binop) : Z :=
  match op with
  | O_Plus => 0
  | O_Minus => 1
  | O_Mul => 2
  | O_Div => 3
  | O_Mod => 4
  | O_Lt => 5
  | O_Eq => 6
  | O_And => 7
  | O_Or => 8
  end.

Ltac destruct_bop op :=
  lazymatch goal with
  | |- context [enum_of_binop op] =>
    destruct op; simpl enum_of_binop;
    repeat match goal with
    | |- semax _ _ (Ssequence (Sifthenelse _ Sbreak Sskip) _) _ => forward
    | |- semax _ _ (Ssequence (Sifthenelse _ Sskip Sbreak) _) _ => forward
    end;
    try lia
  | _ => fail "Can not find corresponding enum_of_binop"
  end.

Inductive expr :=
  | E_Const (v : Z) : expr
  | E_Var (s : val) : expr
  | E_Binop (op : binop) (e1 e2 : expr) : expr
  | E_Deref (e : expr) : expr
  | E_Malloc : expr.

Inductive cmd :=
  | C_Decl (s : val) : cmd
  | C_Asgn (e1 e2 : expr) : cmd
  | C_Seq (c1 c2 : cmd) : cmd
  | C_If (cond : expr) (subt subf : cmd) : cmd
  | C_While (cond : expr) (sub : cmd) : cmd.

Inductive res_prog :=
  | P_Foc (c : cmd) (l : list cmd) : res_prog
  | P_Ectx (h : cmd) (l : list cmd) : res_prog.

Fixpoint expr_rep' (e : expr) (p : val) : mpred :=
  match e with
  | E_Const v =>
      !!(0 <= v <= Int.max_unsigned) &&
      store_expr p 0 v nullval 0 nullval nullval
  | E_Var s =>
      !!(tc_val (tptr tschar) s) &&
      store_expr p 1 0 s 0 nullval nullval
  | E_Binop op e1 e2 => EX arg1 arg2,
      store_expr p 2 0 nullval (enum_of_binop op) arg1 arg2 *
      expr_rep' e1 arg1 *
      expr_rep' e2 arg2
  | E_Deref e => EX arg1,
      store_expr p 3 0 nullval 0 arg1 nullval *
      expr_rep' e arg1
  | E_Malloc =>
      store_expr p 4 0 nullval 0 nullval nullval
  end.

Definition expr_rep (p : val) : mpred :=
  EX e:expr, expr_rep' e p.

Ltac destruct_expr e :=
  lazymatch goal with
  | |- context [expr_rep' e _] =>
    let arg1 := fresh "arg" in
    let arg2 := fresh "arg" in
    destruct e; simpl expr_rep';
      [ Intros
      | Intros
      | Intros arg1 arg2
      | Intros arg1
      | Intros ];
    forward;
    repeat match goal with
    | |- semax _ _ (Ssequence (Sifthenelse _ Sbreak Sskip) _) _ => forward
    | |- semax _ _ (Ssequence (Sifthenelse _ Sskip Sbreak) _) _ => forward
    end;
    try lia
  | _ => fail "Can not find corresponding expr_rep'"
  end.

Fixpoint cmd_rep' (c : cmd) (p : val) : mpred :=
  match c with
  | C_Decl s =>
      !!(tc_val (tptr tschar) s) &&
      store_cmd p 0 s nullval nullval nullval nullval
  | C_Asgn e1 e2 => EX arg1 arg2,
      store_cmd p 1 nullval arg1 arg2 nullval nullval *
      expr_rep' e1 arg1 *
      expr_rep' e2 arg2
  | C_Seq c1 c2 => EX sub1 sub2,
      store_cmd p 2 nullval nullval nullval sub1 sub2 *
      cmd_rep' c1 sub1 *
      cmd_rep' c2 sub2
  | C_If cond subt subf => EX arg1 sub1 sub2,
      store_cmd p 3 nullval arg1 nullval sub1 sub2 *
      expr_rep' cond arg1 *
      cmd_rep' subt sub1 *
      cmd_rep' subf sub2
  | C_While cond sub => EX arg1 sub1,
      store_cmd p 4 nullval arg1 nullval sub1 nullval *
      expr_rep' cond arg1 *
      cmd_rep' sub sub1
  end.

Definition cmd_rep (p : val) : mpred :=
  EX c:cmd, cmd_rep' c p.

Ltac destruct_cmd c :=
  lazymatch goal with
  | |- context [cmd_rep' c _] =>
    let arg1 := fresh "arg" in
    let arg2 := fresh "arg" in
    let sub1 := fresh "sub" in
    let sub2 := fresh "sub" in
    destruct c; simpl cmd_rep';
      [ Intros
      | Intros arg1 arg2
      | Intros sub1 sub2
      | Intros arg1 sub1 sub2
      | Intros arg1 sub1 ];
    forward;
    repeat match goal with
    | |- semax _ _ (Ssequence (Sifthenelse _ Sbreak Sskip) _) _ => forward
    | |- semax _ _ (Ssequence (Sifthenelse _ Sskip Sbreak) _) _ => forward
    end;
    try lia
  | _ => fail "Can not find corresponding cmd_rep'"
  end.

Fixpoint cont_list_rep' (l : list cmd) (p : val) : mpred :=
  match l with
  | nil     => !!(p = nullval) && emp
  | c :: l' => EX cp link,
      store_cont_list p cp link *
      cmd_rep' c cp *
      cont_list_rep' l' link
  end.

Definition cont_list_rep (p : val) : mpred :=
  EX l, cont_list_rep' l p.

Definition prog_rep' (pr : res_prog) (p : val) : mpred :=
  match pr with
  | P_Foc c l => EX foc ectx,
      store_res_prog p foc ectx *
      cmd_rep' c foc *
      cont_list_rep' l ectx
  | P_Ectx c l => EX ectx,
      store_res_prog p nullval ectx *
      cont_list_rep' (c :: l) ectx
  end.

Definition prog_rep_or_end' (pr : option res_prog) (p : val) : mpred :=
  match pr with
  | Some pr => prog_rep' pr p
  | None => store_res_prog p nullval nullval
  end.

Definition prog_rep_or_end (p : val) : mpred :=
  EX pr, prog_rep_or_end' pr p.

Definition prog_rep (p : val) : mpred :=
  EX pr:res_prog, prog_rep' pr p.

Lemma expr_rep'_local_facts:
  forall e p,
    expr_rep' e p |-- !!(isptr p).
Proof.
  induction e; simpl expr_rep'; intros; normalize; entailer!.
Qed.

Lemma expr_rep_local_facts:
  forall p,
    expr_rep p |-- !!(isptr p).
Proof.
  intros; unfold expr_rep.
  Intros e. apply expr_rep'_local_facts.
Qed.

Hint Resolve expr_rep'_local_facts: saturate_local.
Hint Resolve expr_rep_local_facts: saturate_local.

Lemma expr_rep'_valid_pointer:
  forall e p,
    expr_rep' e p |-- valid_pointer p.
Proof.
  intros.
  destruct e; simpl; normalize; auto with valid_pointer.
Qed.

Lemma expr_rep_valid_pointer:
  forall p,
    expr_rep p |-- valid_pointer p.
Proof.
  intros; unfold expr_rep.
  Intros e. apply expr_rep'_valid_pointer.
Qed.

Hint Resolve expr_rep'_valid_pointer: valid_pointer.
Hint Resolve expr_rep_valid_pointer: valid_pointer.

Lemma cmd_rep'_local_facts:
  forall c p,
    cmd_rep' c p |-- !!(isptr p).
Proof.
  induction c; simpl cmd_rep'; intros; normalize; entailer!.
Qed.

Lemma cmd_rep_local_facts:
  forall p,
    cmd_rep p |-- !!(isptr p).
Proof.
  intros; unfold cmd_rep.
  Intros c. apply cmd_rep'_local_facts.
Qed.

Hint Resolve cmd_rep'_local_facts: saturate_local.
Hint Resolve cmd_rep_local_facts: saturate_local.

Lemma cmd_rep'_valid_pointer:
  forall c p,
    cmd_rep' c p |-- valid_pointer p.
Proof.
  intros.
  destruct c; simpl; normalize; auto with valid_pointer.
Qed.

Lemma cmd_rep_valid_pointer:
  forall p,
    cmd_rep p |-- valid_pointer p.
Proof.
  intros; unfold cmd_rep.
  Intros c. apply cmd_rep'_valid_pointer.
Qed.

Hint Resolve cmd_rep'_valid_pointer: valid_pointer.
Hint Resolve cmd_rep_valid_pointer: valid_pointer.

Lemma cont_list_rep'_local_facts:
  forall l p,
     cont_list_rep' l p
     |-- !!(is_pointer_or_null p /\ (p = nullval <-> l = nil)).
Proof.
  intros. revert p.
  induction l; simpl cont_list_rep'; intros; normalize; entailer!.
  - intuition.
  - split; intro. subst p. destruct H; contradiction. inv H2.
Qed.

Lemma cont_list_rep_local_facts:
  forall p,
     cont_list_rep p
     |-- !!(is_pointer_or_null p).
Proof.
  intros. unfold cont_list_rep.
  Intros l. sep_apply cont_list_rep'_local_facts.
  entailer!.
Qed.

Hint Resolve cont_list_rep'_local_facts : saturate_local.
Hint Resolve cont_list_rep_local_facts : saturate_local.

Lemma cont_list_rep'_valid_pointer:
  forall l p,
    cont_list_rep' l p |-- valid_pointer p.
Proof.
  destruct l; simpl cont_list_rep'; intros; normalize; entailer!.
Qed.

Lemma cont_list_rep_valid_pointer:
  forall p,
    cont_list_rep p |-- valid_pointer p.
Proof.
  intros. unfold cont_list_rep.
  Intros l. apply cont_list_rep'_valid_pointer.
Qed.

Hint Resolve cont_list_rep'_valid_pointer : valid_pointer.
Hint Resolve cont_list_rep_valid_pointer : valid_pointer.

Theorem store_cont_list_rep :
  forall (c link v : val),
    store_cont_list v c link *
    cmd_rep c *
    cont_list_rep link
    |-- cont_list_rep v.
Proof.
  intros.
  unfold cmd_rep. Intros c'.
  unfold cont_list_rep. Intros l.
  Exists (c' :: l).
  simpl. Exists c link. cancel.
Qed.

Lemma store_op_sameloc_eq:
  forall p op1 op2,
    (store_int p (enum_of_binop op1) * TT) &&
    (store_int p (enum_of_binop op2) * TT)
    |-- !! (op1 = op2).
Proof.
  intros. eapply derives_trans.
  apply data_at_tint_samevalue.
  apply prop_derives. intros.
  apply Vint_injective in H.
  assert (enum_of_binop op1 = enum_of_binop op2).
  { destruct op1; destruct op2; simpl enum_of_binop; prove_int_eq. }
  destruct op1; destruct op2; try discriminate H0; auto.  
Qed.

Hint Resolve store_op_sameloc_eq: precise_rel.

Ltac solve_eq :=
  unfold_data_at_composite;
  do_on_both saturate_local;
  repeat rewrite <- sepcon_assoc;
  left_assoc_sepcon_TT_to_fold_right;
  subst_data_at_sameloc_eq;
  first [discriminate | apply prop_right; congruence].

Lemma expr_rep'_sameloc_eq:
  forall e1 e2 p,
    (expr_rep' e1 p * TT) && (expr_rep' e2 p * TT)
    |-- !! (e1 = e2).
Proof.
  intros e1.
  induction e1; intros; unfold_once expr_rep';
    destruct e2; simpl expr_rep'; normalize; solve_eq.
Qed.

Hint Resolve expr_rep'_sameloc_eq: precise_rel.

Lemma cmd_rep'_sameloc_eq:
  forall c1 c2 p,
    (cmd_rep' c1 p * TT) && (cmd_rep' c2 p * TT)
    |-- !! (c1 = c2).
Proof.
  intros c1.
  induction c1; intros; unfold_once cmd_rep';
    destruct c2; simpl cmd_rep'; normalize; solve_eq.
Qed.

Hint Resolve cmd_rep'_sameloc_eq: precise_rel.

Lemma cont_list_rep'_sameloc_eq:
  forall l1 l2 p,
    (cont_list_rep' l1 p * TT) && (cont_list_rep' l2 p * TT)
    |-- !! (l1 = l2).
Proof.
  intros l1.
  induction l1; intros; unfold_once cont_list_rep';
    destruct l2; simpl cont_list_rep'; normalize.
  - data_at_nullval_left.
  - data_at_nullval_left.
  - solve_eq.
Qed.

Hint Resolve cont_list_rep'_sameloc_eq: precise_rel.

Lemma prog_rep'_sameloc_eq:
  forall p1 p2 p,
    (prog_rep' p1 p * TT) && (prog_rep' p2 p * TT)
    |-- !! (p1 = p2).
Proof.
  intros. destruct p1, p2; simpl prog_rep'; normalize.
  - solve_eq.
  - unfold_data_at_composite.
    do_on_both saturate_local.
    repeat rewrite <- sepcon_assoc.
    left_assoc_sepcon_TT_to_fold_right.
    subst_data_at_sameloc_eq.
    inv Px.
  - unfold_data_at_composite.
    do_on_both saturate_local.
    repeat rewrite <- sepcon_assoc.
    left_assoc_sepcon_TT_to_fold_right.
    apply data_at_tptr_sameloc_eq; [intuition | intros <-].
    inv Pectx.
  - do_on_both saturate_local. solve_eq.
Qed.

Hint Resolve prog_rep'_sameloc_eq: precise_rel.

Lemma prog_rep_or_end'_sameloc_eq:
  forall p1 p2 p,
    (prog_rep_or_end' p1 p * TT) && (prog_rep_or_end' p2 p * TT)
    |-- !! (p1 = p2).
Proof.
  intros. destruct p1, p2; simpl prog_rep_or_end'; normalize.
  - solve_eq.
  - destruct r; simpl prog_rep'; normalize.
    + unfold_data_at_composite.
      do_on_both saturate_local.
      repeat rewrite <- sepcon_assoc.
      left_assoc_sepcon_TT_to_fold_right.
      subst_data_at_sameloc_eq. inv Pfoc.
    + do_on_both saturate_local.
      unfold_data_at_composite.
      do_on_both saturate_local.
      repeat rewrite <- sepcon_assoc.
      left_assoc_sepcon_TT_to_fold_right.
      subst_data_at_sameloc_eq. inv H1. inv H14.
  - destruct r; simpl prog_rep'; normalize.
    + unfold_data_at_composite.
      do_on_both saturate_local.
      repeat rewrite <- sepcon_assoc.
      left_assoc_sepcon_TT_to_fold_right.
      apply data_at_tptr_sameloc_eq; [intuition | intros <-].
      inv Pfoc.
    + do_on_both saturate_local.
      unfold_data_at_composite.
      do_on_both saturate_local.
      repeat rewrite <- sepcon_assoc.
      left_assoc_sepcon_TT_to_fold_right.
      apply data_at_tptr_sameloc_eq; [intuition | intros _].
      apply data_at_tptr_sameloc_eq; [intuition | intros <-].
      inv H2. inv H14.
Qed.

Hint Resolve prog_rep_or_end'_sameloc_eq: precise_rel.

Lemma precise_expr_rep':
  forall e p,
    precise_pred (expr_rep' e p).
Proof.
  intros e.
  induction e; intros; simpl expr_rep'.
  - apply andp_prop_precise.
    unfold_data_at_composite. prove_precise_pred_sepcon.
  - apply andp_prop_precise.
    unfold_data_at_composite. prove_precise_pred_sepcon.
  - repeat rewrite exp_uncurry. apply exp_precise.
    + intros. destruct_all. solve_eq.
    + intros. unfold_data_at_composite. prove_precise_pred_sepcon; auto.
  - apply exp_precise.
    + intros. solve_eq.
    + intros. unfold_data_at_composite. prove_precise_pred_sepcon; auto.
  - unfold_data_at_composite. prove_precise_pred_sepcon.
Qed.

Hint Resolve precise_expr_rep': precise_pred.

Lemma precise_expr_rep:
  forall p,
    precise_pred (expr_rep p).
Proof.
  intros. unfold expr_rep.
  apply exp_precise.
  - intros. apply expr_rep'_sameloc_eq.
  - intros. apply precise_expr_rep'.
Qed.

Hint Resolve precise_expr_rep: precise_pred.

Lemma precise_cmd_rep':
  forall c p,
    precise_pred (cmd_rep' c p).
Proof.
  intros c.
  induction c; intros; simpl cmd_rep'.
  - apply andp_prop_precise.
    unfold_data_at_composite. prove_precise_pred_sepcon.
  - repeat rewrite exp_uncurry. apply exp_precise.
    + intros. destruct_all. solve_eq.
    + intros. unfold_data_at_composite. prove_precise_pred_sepcon; auto.
  - repeat rewrite exp_uncurry. apply exp_precise.
    + intros. destruct_all. solve_eq.
    + intros. unfold_data_at_composite. prove_precise_pred_sepcon; auto.
  - repeat rewrite exp_uncurry. apply exp_precise.
    + intros. destruct_all. solve_eq.
    + intros. unfold_data_at_composite. prove_precise_pred_sepcon; auto.
  - repeat rewrite exp_uncurry. apply exp_precise.
    + intros. destruct_all. solve_eq.
    + intros. unfold_data_at_composite. prove_precise_pred_sepcon; auto.
Qed.

Hint Resolve precise_cmd_rep': precise_pred.

Lemma precise_cmd_rep:
  forall p,
    precise_pred (cmd_rep p).
Proof.
  intros. unfold cmd_rep.
  apply exp_precise.
  - intros. apply cmd_rep'_sameloc_eq.
  - intros. apply precise_cmd_rep'.
Qed.

Hint Resolve precise_cmd_rep: precise_pred.

Lemma precise_cont_list_rep':
  forall l p,
    precise_pred (cont_list_rep' l p).
Proof.
  intros l.
  induction l; intros; simpl cont_list_rep'.
  - apply andp_prop_precise. apply precise_emp.
  - rewrite exp_uncurry. apply exp_precise.
    + intros. destruct_all. solve_eq.
    + intros. unfold_data_at_composite. prove_precise_pred_sepcon.
Qed.

Hint Resolve precise_cont_list_rep': precise_pred.

Lemma precise_cont_list_rep:
  forall p,
    precise_pred (cont_list_rep p).
Proof.
  intros. unfold cont_list_rep.
  apply exp_precise.
  - intros. apply cont_list_rep'_sameloc_eq.
  - intros. apply precise_cont_list_rep'.
Qed.

Hint Resolve precise_cont_list_rep: precise_pred.

Lemma precise_prog_rep':
  forall pr p,
    precise_pred (prog_rep' pr p).
Proof.
  intros pr.
  destruct pr; intros; unfold prog_rep'.
  - rewrite exp_uncurry. apply exp_precise.
    + intros. destruct_all. solve_eq.
    + intros. unfold_data_at_composite. prove_precise_pred_sepcon.
  - apply exp_precise.
    + intros. solve_eq.
    + intros. unfold_data_at_composite. prove_precise_pred_sepcon.
Qed.

Hint Resolve precise_prog_rep': precise_pred.

Lemma precise_prog_rep:
  forall p,
    precise_pred (prog_rep p).
Proof.
  intros. unfold prog_rep.
  apply exp_precise.
  - intros. apply prog_rep'_sameloc_eq.
  - intros. apply precise_prog_rep'.
Qed.

Hint Resolve precise_prog_rep: precise_pred.

Lemma precise_prog_rep_or_end':
  forall pr p,
    precise_pred (prog_rep_or_end' pr p).
Proof.
  intros pr.
  destruct pr; intros; unfold prog_rep_or_end'.
  - apply precise_prog_rep'.
  - unfold_data_at_composite. prove_precise_pred_sepcon.
Qed.

Hint Resolve precise_prog_rep_or_end': precise_pred.

Lemma precise_prog_rep_or_end:
  forall p,
    precise_pred (prog_rep_or_end p).
Proof.
  intros. unfold prog_rep_or_end.
  apply exp_precise.
  - intros. apply prog_rep_or_end'_sameloc_eq.
  - intros. apply precise_prog_rep_or_end'.
Qed.

Hint Resolve precise_prog_rep_or_end: precise_pred.

Parameter precise_hash_table_rep: forall p, precise_pred (hash_table_rep p).
Parameter precise_memory_rep: forall p, precise_pred (memory_rep p).

Hint Resolve precise_hash_table_rep precise_memory_rep: precise_pred.
