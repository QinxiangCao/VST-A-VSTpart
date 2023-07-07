Require Import utils.VSTALib.

Require Import cprogs.swap.program.
Require Import cprogs.swap.definitions.
Require Import cprogs.swap.annotation.
Require cprogs.swap.int_pair_swap2.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.swap.int_pair_swap2.path0.

Ltac field_address_solver :=
  match goal with
  | |- @eq val ?p (field_address _ _ ?p) => idtac
  | |- @eq val (offset_val _ ?p) (field_address _ _ ?p) => idtac
  | |- @eq val (field_address _ _ ?p) ?p => idtac
  | |- @eq val (field_address _ _ ?p) (offset_val _ ?p) => idtac
  | _ => fail 1 "The proof goal is not in a form of (p = field_address _ _ p) or (offset_val _ p = field_address _ _ p)"
  end;
  unfold field_address; simpl;
  (rewrite if_true by auto with field_compatible || fail 1 "Not enough field_compatible information to derive the equality.");
  rewrite ? isptr_offset_val_zero; auto.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros.
  subst p'.
  unfold_data_at (store_int_pair p0 x y).
  forward_call (y, x, (field_address (Tstruct _int_pair noattr) [StructField _b] p0), (field_address (Tstruct _int_pair noattr) [StructField _a] p0) , (field_address (Tstruct _int_pair noattr) [StructField _a] p0), (field_address (Tstruct _int_pair noattr) [StructField _b] p0) ).
  {
    entailer!.
    split; f_equal; field_address_solver.
  }
  {
    entailer!.
  }
  unfold RA_normal, normal_split_assert.
  entailer!.
  unfold_data_at (store_int_pair p0 y x).
  entailer!.
Qed.

End SH_Proof.

