From compcert Require Export common.AST cfrontend.Ctypes cfrontend.Clight.
Export Cop.
Require Export FloydSeq.base2.
Require Export VST.floyd.functional_base.
Require Export FloydSeq.client_lemmas.
Require Export FloydSeq.go_lower.
Require Export FloydSeq.closed_lemmas.
Require Export FloydSeq.compare_lemmas.
Require Export FloydSeq.semax_tactics.
Require Export FloydSeq.entailer.
Require Export FloydSeq.forward. (* must come after entailer because of Ltac override *)
Require Export FloydSeq.subsume_funspec.
Require Export FloydSeq.call_lemmas.
Require Export FloydSeq.forward_lemmas.
Require Export FloydSeq.for_lemmas.
Require Export FloydSeq.nested_pred_lemmas.
Require Export FloydSeq.nested_field_lemmas.
Require Export FloydSeq.efield_lemmas.
Require Export FloydSeq.mapsto_memory_block.
Require Export FloydSeq.aggregate_type.
Require FloydSeq.aggregate_pred. Export FloydSeq.aggregate_pred.aggregate_pred.
Require Export FloydSeq.reptype_lemmas.
Require Export FloydSeq.simpl_reptype.
Require Export FloydSeq.data_at_rec_lemmas.
Require Export FloydSeq.field_at.
Require Export FloydSeq.field_at_wand.
Require Export FloydSeq.field_compat.
Require Export FloydSeq.stronger.
Require Export FloydSeq.loadstore_mapsto.
Require Export FloydSeq.loadstore_field_at.
Require Export FloydSeq.nested_loadstore.
Require Export FloydSeq.local2ptree_denote.
Require Export FloydSeq.local2ptree_eval.
Require Export FloydSeq.local2ptree_typecheck.
Require Export FloydSeq.proj_reptype_lemmas.
Require Export FloydSeq.replace_refill_reptype_lemmas.
Require Export FloydSeq.sc_set_load_store.
Require Export FloydSeq.unfold_data_at.
Require Export FloydSeq.globals_lemmas.
Require Export FloydSeq.diagnosis.
Require Export FloydSeq.freezer.
Require Export FloydSeq.deadvars.
Require Export FloydSeq.hints.
Require Export FloydSeq.Clightnotations.
Require Export FloydSeq.list_solver.
Require Export FloydSeq.data_at_lemmas.
Require VST.msl.iter_sepcon.
Require VST.msl.wand_frame.
Require VST.msl.wandQ_frame.
Require FloydSeq.linking.

Arguments semax {CS} {Espec} Delta Pre%assert cmd%C Post%assert.
Export ListNotations.
Export Clight_Cop2.

Hint Rewrite add_repr mul_repr sub_repr : entailer_rewrite.
Hint Rewrite ptrofs_add_repr ptrofs_mul_repr ptrofs_sub_repr : entailer_rewrite.
Hint Rewrite mul64_repr add64_repr sub64_repr or64_repr and64_repr : entailer_rewrite.
Hint Rewrite neg_repr neg64_repr : entailer_rewrite.
Hint Rewrite ptrofs_to_int_repr: entailer_rewrite norm.
Hint Rewrite ptrofs_to_int64_repr using reflexivity: entailer_rewrite norm.

Lemma Vptrofs_unfold_false: 
Archi.ptr64 = false -> Vptrofs = fun x => Vint (Ptrofs.to_int x).
Proof.
intros. unfold Vptrofs.
extensionality x.
rewrite H.
auto.
Qed.

Lemma Vptrofs_unfold_true: 
Archi.ptr64 = true -> Vptrofs = fun x => Vlong (Ptrofs.to_int64 x).
Proof.
intros. unfold Vptrofs.
extensionality x.
rewrite H.
auto.
Qed.

Lemma modu_repr: forall x y, 
   0 <= x <= Int.max_unsigned ->
   0 <= y <= Int.max_unsigned ->
  Int.modu (Int.repr x) (Int.repr y) = Int.repr (x mod y).
Proof.
intros. unfold Int.modu. rewrite !Int.unsigned_repr by auto. auto.
Qed.
Hint Rewrite modu_repr using rep_omega : entailer_rewrite norm.

Hint Rewrite Vptrofs_unfold_false using reflexivity: entailer_rewrite norm.
Hint Rewrite Vptrofs_unfold_true using reflexivity: entailer_rewrite norm.

Hint Extern 1 (Vundef = default_val _) => reflexivity : cancel.
Hint Extern 1 (default_val _ = Vundef) => reflexivity : cancel.
Hint Extern 1 (list_repeat _ Vundef = default_val _) => reflexivity : cancel.
Hint Extern 1 (default_val _ = list_repeat _ Vundef) => reflexivity : cancel.
Hint Extern 1 (Vundef :: _ = default_val _) => reflexivity : cancel.
Hint Extern 1 (default_val _ = Vundef :: _) => reflexivity : cancel.
Hint Extern 1 (@nil _ = default_val _) => reflexivity : cancel.
Hint Extern 1 (default_val _ = @nil _) => reflexivity : cancel.

Instance Inhabitant_mpred : Inhabitant mpred := @FF mpred Nveric.
Instance Inhabitant_share : Inhabitant share := Share.bot.

Arguments deref_noload ty v / .
Arguments nested_field_array_type {cs} t gfs lo hi / .
Arguments nested_field_type {cs} t gfs / .  (* redundant? *)
Arguments nested_field_offset {cs} t gfs / .  (* redundant? *)
Arguments Z.mul !x !y.
Arguments Z.sub !m !n.
Arguments Z.add !x !y.
Global Transparent peq.
Global Transparent Archi.ptr64.

Hint Resolve readable_Ers : core.

Ltac EExists_unify1 x P :=
 match P with
 | ?P1 /\ ?P2 => first [EExists_unify1 x P1 | EExists_unify1 x P2]
 | ?A = ?B =>
  match A with context [x] =>
  pattern (A=B);
  let y := fresh "y" in match goal with |- ?F _ => set (y:=F) end;
  autorewrite with entailer_rewrite;
  first  [subst x; match goal with |- _ (?A' = ?B') => unify A' B' end
  | match goal with
  | x:= ?u |- _ (Vint (Int.repr (x - ?i)) = Vint (Int.repr ?j)) =>
        unify u (j+i); subst x
  | x:= ?u |- _ (Vint (Int.repr (x + ?i)) = Vint (Int.repr ?j)) =>
        unify u (j-i); subst x
  | x:= ?u |- _ (Vlong (Int64.repr (x - ?i)) = Vlong (Int64.repr ?j)) =>
        unify u (j+i); subst x
  | x:= ?u |- _ (Vlong (Int64.repr (x + ?i)) = Vlong (Int64.repr ?j)) =>
        unify u (j-i); subst x
  end];
  subst y; cbv beta
  end
end.

Ltac EExists_unify := 
  let T := fresh "T"  in
  let x := fresh "x" in
  evar (T:Type); evar (x:T); subst T; 
  Exists x;
  match goal with
  | |- _ |-- !! ?P && _ => EExists_unify1 x P
  | |- _ |-- !! ?P => EExists_unify1 x P
  end.

Ltac simpl_implicit :=
  simpl projT1.

Ltac step :=
  first
  [ progress Intros
  | let x := fresh "x" in Intros x
  | progress simpl_implicit
  | progress autorewrite with sublist in *|-
  | progress autorewrite with sublist
  | progress autorewrite with norm
  | forward
  | forward_if
  | forward_call
  | rep_omega | cstring' | list_solve
  | match goal with |- ENTAIL _, _ |-- _ =>  go_lower end
  | EExists_unify
  | cstring1
  | deadvars!
  | solve [match goal with |- @derives mpred _ _ _ => cancel end]
  | solve [entailer!; try cstring']
  | list_solve!
  ].

Tactic Notation "step!"  :=
  first
  [ progress Intros
  | let x := fresh "x" in
    Intros x
  | progress simpl_implicit
  | progress autorewrite with sublist in * |-
  | progress autorewrite with sublist
  | progress autorewrite with norm
  | forward
  | forward_if
  | forward_call
  | rep_omega
  | cstring'
  | list_solve
  | EExists
  | cstring1
  | deadvars!
  | progress_entailer
  (* | match goal with |- _ /\ _ => split end *)
  | list_solve!
  ].

Tactic Notation "info_step!" :=
  first
  [ progress Intros; idtac "Intros."
  | let x := fresh "x" in
    Intros x;
    idtac "Intros x."
  | progress simpl_implicit; idtac "simpl_implicit."
  | progress autorewrite with sublist in * |-; idtac "autorewrite with sublist in * |-."
  | progress autorewrite with sublist; idtac "autorewrite with sublist."
  | progress autorewrite with norm; idtac "autorewrite with norm."
  | forward; idtac "forward."
  | forward_if; idtac "forward_if."
  | forward_call; idtac "forward_call."
  | rep_omega; idtac "rep_omega."
  | cstring'; idtac "cstring'."
  | list_solve; idtac "list_solve."
  | EExists; idtac "EExists."
  | cstring1; idtac "cstring1."
  | deadvars!; idtac "deadvars!."
  | progress_entailer; idtac "progress_entailer."
  (* | match goal with |- _ /\ _ => split end; idtac "split." *)
  | list_solve!; idtac "list_solve!."
  ].

(* A better way to deal with sem_cast_i2bool *)
Lemma sem_cast_i2bool_of_bool : forall (b : bool),
  sem_cast_i2bool (Val.of_bool b) = Some (Val.of_bool b).
Proof.
  destruct b; auto.
Qed.
Hint Rewrite sem_cast_i2bool_of_bool : norm.

Hint Extern 1 (@eq Z _ _) => Zlength_solve : Zlength_solve.
Hint Extern 1 (@eq _ _ _) => f_equal : f_equal.

Ltac list_solve ::= Zlength_solve.
