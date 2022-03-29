Require Import CSplit.soundness.

(* 
int sgn (int x) {
  //@ With x:Z,
  //@ Require PROP (Int.min_signed <= x <= Int.max_signed) LOCAL (temp _x  (Vint (Int.repr x))) SEP ()
  //@ Ensure PROP () LOCAL (temp ret_temp  (Vint (Int.repr (sgn x)))) SEP ()
  int ret;
  if (x <= 0) {
    if(x == 0)
      ret = 0;
    else
      ret = -1;
  }
  else
    ret = 1;
  return ret;
} 
*)

Require Import CSplit.AClight.

Arguments Cifthenelse _ {_ _} _ _.
Arguments Csequence {_ _ } _ _.
Arguments Cloop {_ _} _ _.

(* Examples: *)
Parameter _ret : ident.
Parameter _x : ident.

Definition sgn_S :=
(Ssequence Sassert
  (Ssequence
  (Sifthenelse (Ebinop Ole (Etempvar _x tint) (Econst_int (Int.repr 0) tint)
                  tint)
      (Sifthenelse (Ebinop Oeq (Etempvar _x tint)
                      (Econst_int (Int.repr 0) tint) tint)
      (Sset _ret (Econst_int (Int.repr 0) tint))
      (Sset _ret (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
      (Sset _ret (Econst_int (Int.repr 1) tint)))
  (Sreturn (Some (Etempvar _ret tint))))).

Ltac cbv_conns := cbv [
  atom_conn_return
  atom_conn_returns
  atoms_conn_returns
  atom_conn_atom
  atom_conn_atoms
  atoms_conn_atoms
  atom_conn_Spre
  atom_conn_Spres
  atoms_conn_Spres
  Spost_conn_atom
  Sposts_conn_atom
  Spost_conn_return
  Sposts_conn_return
  Sposts_conn_atoms
  Sposts_conn_returns
  Spost_conn_Spre
  Sposts_conn_Spres
  add_exp_to_Spre
  add_exp_to_Spres
  add_exp_to_atom
  add_exp_to_atoms
  add_exp_to_ret_atom
  add_exp_to_ret_atoms
  add_P_to_Spre
  add_P_to_atom
  add_P_to_atom_ret
  add_Q_to_Spost
  add_Q_to_atom
  add_Q_to_atoms

  atom_conn_Cpre
  atom_conn_Cpres
  atoms_conn_Cpres
  Cpost_conn_atom
  Cposts_conn_atom
  Cposts_conn_atoms
  Cpost_conn_return
  Cposts_conn_return
  Cposts_conn_returns
  Cpost_conn_Cpre_aux
  Cpost_conn_Cpre
  Cpost_conn_Cpres
  Cposts_conn_Cpres
  add_exp_to_Cpre
  add_exp_to_Cpres
  add_P_to_Cpre
  add_P_to_Cpres
  add_P_to_Catoms
  add_P_to_Catom_rets
  add_Q_to_Cpost
  add_Q_to_Cposts
  add_Q_to_Catoms

  add_exP_to_Cpre
].

Ltac unfold_split := cbv [
  S_split_sequence
  S_split_ifthenelse
  S_split_loop
  S_split_loop_refined
  S_split_assert
  S_split_skip
  S_split_assign
  S_split_call
  S_split_set
  S_split_break
  S_split_continue
  S_split_return

  S_split

  C_split_assert
  C_split_sequence
  C_split_skip
  C_split_assign
  C_split_call
  C_split_set
  C_split_break
  C_split_continue
  C_split_return
  C_split_ifthenelse
  C_split_loop
  C_split_loop_refined

  C_split
].


(* Ltac unfold_der := cbv [app map      
  add_exp_to_Spres add_exp_to_Cpres
  add_exp_to_atoms add_exp_to_ret_atoms


  atoms_conn_atoms Sposts_conn_atoms Sposts_conn_returns
  Sposts_conn_Spres Cposts_conn_atoms Cposts_conn_returns
  Cposts_conn_Cpres Cposts_conn_return Capp Cmap
  atoms_conn_Cpres
  atoms_conn_Spres
  atoms_conn_returns
  atom_conn_returns
  atom_conn_return
  concat
  add_exp_to_atom
  atom_conn_atoms
  atom_conn_Spres
  atom_conn_Cpres
  Sposts_conn_return
  Cposts_conn_return
  Cpost_conn_return
  Spost_conn_return
]. *)






Definition sgn_C :=
Cexgiven Z (fun x => (PROP (Int.min_signed <= x <= Int.max_signed) LOCAL (temp _x  (Vint (Int.repr x))) SEP ())) _
(fun x =>

(Csequence
(Cifthenelse 
    (Ebinop Ole (Etempvar _x tint) (Econst_int (Int.repr 0) tint) tint)
    (Cifthenelse (Ebinop Oeq (Etempvar _x tint)
                    (Econst_int (Int.repr 0) tint) tint)
    (Cset _ret (Econst_int (Int.repr 0) tint))
    (Cset _ret (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
    (Cset _ret (Econst_int (Int.repr 1) tint)))
(Creturn (Some (Etempvar _ret tint))))
).


Goal (C_split sgn_S sgn_C) = (C_split sgn_S sgn_C).
unfold sgn_S. unfold sgn_C.
unfold_split.
unfold_der.
cbv_conns.


Compute (S_split sgn_S).





Goal (C_split sgn_S sgn_C) = (C_split sgn_S sgn_C).
unfold C_split. unfold S_split. unfold sgn_C. unfold sgn_S.
cbv [C_split_set S_split_set S_split_ifthenelse C_split_ifthenelse S_split_sequence C_split_sequence
S_split_return C_split_return
].
unfold_der.



cbv [C_split_exgiven].
cbv [add_exP_to_Cpre].
cbv [C_result_proj_C_post_break C_result_proj_C_post_normal
C_result_proj_C_path C_result_proj_C_post_continue
C_result_proj_C_post_return
].
cbv [
  flatten_partial_posts_binds
  flatten_full_paths_binds
  flatten_partial_post_rets_binds
  flatten_binds
].
unfold_der.
reflexivity.
Qed.

Ltac compute_split s_stm c_stm :=
let res1 := eval cbv delta [C_split S_split s_stm c_stm] in (C_split s_stm c_stm) in
let res2 := eval cbv [C_split_set S_split_set S_split_ifthenelse C_split_ifthenelse S_split_sequence C_split_sequence
S_split_return C_split_return
] in res1 in
let res3 := eval cbv [app map add_exp_to_Spres add_exp_to_Cpres add_exp_to_atoms add_exp_to_ret_atoms
atoms_conn_atoms Sposts_conn_atoms Sposts_conn_returns
Sposts_conn_Spres Cposts_conn_atoms Cposts_conn_returns
Cposts_conn_Cpres Cposts_conn_return Capp Cmap
atoms_conn_Cpres
atoms_conn_Spres
atoms_conn_returns
atom_conn_returns
atom_conn_return
concat
add_exp_to_atom
atom_conn_atoms
atom_conn_Spres
atom_conn_Cpres
Sposts_conn_return
Cposts_conn_return
Cpost_conn_return
Spost_conn_return
] in res2 in
exact res3.

Definition res :=
  ltac:(compute_split sgn_S sgn_C).

Print res.
  C_result_proj_C_pre
].

unfold C_split_exgiven.

simpl.


Compute (C_split sgn_S sgn_C).




(* 
All split functions:

atom_conn_return
atom_conn_returns
atoms_conn_returns
atom_conn_atom
atom_conn_atoms
atoms_conn_atoms
atom_conn_Spre
atom_conn_Spres
atoms_conn_Spres
Spost_conn_atom
Sposts_conn_atom
Spost_conn_return
Sposts_conn_return
Sposts_conn_atoms
Sposts_conn_returns
Spost_conn_Spre
Sposts_conn_Spres
add_exp_to_Spre
add_exp_to_Spres
add_exp_to_atom
add_exp_to_atoms
add_exp_to_ret_atom
add_exp_to_ret_atoms
add_P_to_Spre
add_P_to_atom
add_P_to_atom_ret
add_Q_to_Spost
add_Q_to_atom
add_Q_to_atoms

atom_conn_Cpre
atom_conn_Cpres
atoms_conn_Cpres
Cpost_conn_atom
Cposts_conn_atom
Cposts_conn_atoms
Cpost_conn_return
Cposts_conn_return
Cposts_conn_returns
Cpost_conn_Cpre_aux
Cpost_conn_Cpre
Cpost_conn_Cpres
Cposts_conn_Cpres
add_exp_to_Cpre
add_exp_to_Cpres
add_P_to_Cpre
add_P_to_Cpres
add_P_to_Catoms
add_P_to_Catom_rets
add_Q_to_Cpost
add_Q_to_Cposts
add_Q_to_Catoms

S_split_sequence
S_split_ifthenelse
S_split_loop
S_split_loop_refined
S_split_assert
S_split_skip
S_split_assign
S_split_call
S_split_set
S_split_break
S_split_continue
S_split_return

S_split

hd_of
tl_of
flatten_binds
hd_assert_of_pre
flatten_partial_pres_binds
flatten_partial_posts_binds
flatten_partial_post_rets_binds
flatten_full_paths_binds

C_result_proj_C_pre
C_result_proj_C_post_normal
C_result_proj_C_post_break
C_result_proj_C_post_continue
C_result_proj_C_post_return
C_result_proj_C_path

C_split_assert
C_split_sequence
add_exP_to_Cpre
C_split_exgiven
C_split_skip
C_split_assign
C_split_call
C_split_set
C_split_break
C_split_continue
C_split_return
C_split_ifthenelse
C_split_loop
C_split_loop_refined



 *)