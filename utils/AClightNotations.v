Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Clight.
Require Import Csplit.AClight.
Require Import compcert.common.AST.

Require Import Csplit.semantics.
Require Import Csplit.strongSoundness.
Require Import FloydSeq.proofauto.
Require Import Csplit.AClightFunc.

(* Require Import FloydSeq.forward. *)
(** ** Functions *)

(** A function definition is composed of its return type ([fn_return]),
  the names and types of its parameters ([fn_params]), the names
  and types of its local variables ([fn_vars]), and the body of the
  function (a statement, [fn_body]). *)

Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_temps: list (ident * type);
  fn_body: statement
}.

Definition var_names (vars: list(ident * type)) : list ident :=
  List.map (@fst ident type) vars.

(** Functions can either be defined ([Internal]) or declared as
  external functions ([External]). *)

Definition fundef := Ctypes.fundef function.

(** The type of a function definition. *)

Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).


(* Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end. *)

(** ** Programs *)

(** As defined in module [Ctypes], a program, or compilation unit, is
  composed of:
- a list of definitions of functions and global variables;
- the names of functions and global variables that are public (not static);
- the name of the function that acts as entry point ("main" function).
- a list of definitions for structure and union names
- the corresponding composite environment
- a proof that this environment is consistent with the definitions. *)

Definition program := Ctypes.program function.

(** Generate VST funcspec from annotation funcspec *)

Ltac move_let_inside v :=
  lazymatch goal with
  | v := let (a, b) := _ in _ |- _ =>
    lazymatch goal with
    | v := let (a, b) := ?p in fun x:?T => ?content |- _ =>
      let temp := fresh "temp" in
      let x := fresh x in
      refine (fun x => _);
      pose (temp := (fun x:T => let (a, b) := p in content) x);
      hnf in temp;
      clear v;
      rename temp into v;
      move_let_inside v
    | v := let (a, b) := ?p in (?pre, ?post) |- _ =>
      exact (let (a, b) := p in pre, let (a, b) := p in post)
    | _ => fail 0 v "is not recognized"
    end
  | _ => fail 0 v "must have form let (a, b) := p in _"
  end.

Ltac uncurry_funcspec spec :=
  let spec_name := fresh "spec" in
  let spec := eval unfold spec in spec in
  pose (spec_name := spec);
  repeat
    lazymatch goal with
    | spec_name := fun x:?T1 => fun y:?T2 => ?spec |- _ =>
      first [ignore (T2 : _) | fail 2 "funcspec cannot have dependent type"];
      first [
        let spec_name1 := fresh "spec" in
        pose (spec_name1 := (fun p : (T1*T2) => let (x, y) := p in spec));
        clear spec_name;
        rename spec_name1 into spec_name;
        refine (let spec_name1 :=
          ltac:(
            match goal with
            | spec_name := ?spec |- _ =>
            let spec := eval unfold spec_name in spec_name in
            let p := fresh "p" in
            intro p;
            pose (spec_name1 := spec p);
            hnf in spec_name1;
            clear spec_name;
            rename spec_name1 into spec_name;
            move_let_inside spec_name;
            exact spec_name
            end
          ) in _);
        clear spec_name;
        rename spec_name1 into spec_name;
        cbv beta zeta in spec_name
      | fail 2 "Unknown error: failed to uncurry funcspec"
      ]
    end;
  exact spec_name.

Ltac make_funcspec name funsig spec :=
  let spec := eval cbv beta zeta delta [spec] in spec in
  lazymatch spec with
  | fun x:?T => (?P, ?Q) =>
    exact (name, NDmk_funspec funsig cc_default T (fun x => P) (fun x => Q))
  | _ => fail 0 spec "is not in valid form of funcspec"
  end.


Global Arguments Cifthenelse _ {_ _} _ _.
Global Arguments Csequence {_ _ } _ _.
Global Arguments Cloop {_ _} _ _.
Global Arguments list_binded_cons {_ _ _} _ {_} _.
Global Arguments bind_C_full_path {_ _} _.

Global Arguments C_split {_} _.

Module AClightNotations.

Notation "'ANNOTATION_WITH' x .. y , c " :=
  (fun x => .. (fun y => c) .. ) (at level 65, x binder, y binder).

Notation "'GIVEN' x .. y , c " :=
  (bind_C_full_path (fun x => .. (bind_C_full_path (fun y => c)) ..)) (at level 65, x binder, y binder) : logic.

Notation "'EXGIVEN' x  '[[' ass ']]'  c " :=
  (Cexgiven _ (fun x => ass) _ (fun x => c)) (at level 65) : logic.

Notation "!!"  := semax_lemmas.Cnot.

Notation "{ x ; y ; .. ; z }" := (list_binded_cons x (list_binded_cons y .. (list_binded_cons z list_binded_nil) ..)) : list_scope.

Notation "'assume' '!' e ;" := (Sifthenelse (e%expr) Sbreak Sskip) (only printing, right associativity, at level 26, format "'assume'  '!'  e ;") : C_scope.

Notation "'assume' e ;" := (Sifthenelse (e%expr) Sskip Sbreak) (only printing, right associativity, at level 26, format "'assume'  e ;") : C_scope.

End AClightNotations.

Ltac compute_split c_stm :=
let c_stm' := eval hnf in c_stm in
let res1 := eval cbv [
  C_result

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

  (**************)

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

  Smap Sconcat Sapp Capp Cmap

  (**************)

  hd_of
  tl_of
  flatten_binds
  hd_assert_of_pre
  flatten_partial_pres_binds
  flatten_partial_posts_binds
  flatten_partial_post_rets_binds
  flatten_full_paths_binds
  C_split_exgiven
  add_exP_to_Cpre

C_result_proj_C_pre
C_result_proj_C_post_normal
C_result_proj_C_post_break
C_result_proj_C_post_continue
C_result_proj_C_post_return
C_result_proj_C_path
  
  (**************)

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

  Smap Sconcat Sapp Capp Cmap
] in ((C_split c_stm')) in
    exact res1.

Import AClightNotations.

Ltac start_function_argument_tac HINT_CODE :=
  change @floyd.client_lemmas.abbreviate with @FloydSeq.client_lemmas.abbreviate in *;
  apply semax_derives;
  eapply (soundness _ _ _ _ HINT_CODE); [reflexivity | ..];
  match goal with
  | |- context [C_split ?c] =>
    change (C_split c) with (ltac:(compute_split HINT_CODE))
  end;
  apply split_Semax_fun_equiv;
    cbv [split_Semax_fun S_split S_split_sequence S_split_assert S_split_set S_split_loop_refined S_split_loop S_split_ifthenelse S_split_break S_split_continue S_split_return S_split_skip S_split_assign S_split_call
        path_to_semax pre_to_semax post_to_semax post_ret_to_semax atom_to_semax atom_ret_to_semax 
        hd_assert_of_post hd_assert_of_post_ret
        path_to_statement to_Clight
        atoms_conn_atoms atom_conn_atom atom_conn_atoms atoms_conn_returns atom_conn_returns Sconcat Sapp Smap SForall CForall
        add_exp_to_atom add_exp_to_atoms
        add_exp_to_ret_atom add_exp_to_ret_atoms
        atom_conn_return];
  repeat
    match goal with
    | |- _ /\ _ => split
    | |- True => auto
    | |- _ => intros; simple apply semax_skip_normal_split_post; apply derives_refl
    end.

Ltac VST_A_start_function hint :=
  start_function.start_function hint start_function_argument_tac;
  intros; rewrite semax_remove_skip; simpl remove_skip.

Ltac get_para_type_rec_tac A B :=
  match B with
  | ?B1 -> ?B2 => get_para_type_rec_tac (prod A B1) B2
  | prod _ _ => exact A
  end.

Ltac get_para_type_tac spec_annot :=
  match type of spec_annot with
  | ?A -> prod _ _ => exact A
  | ?A -> ?B => get_para_type_rec_tac A B
  end.

Notation "'GET_PARA_TYPE' x" := ltac:(get_para_type_tac x) (at level 99).

Module Type STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Parameter functional_correctness_statement: Prop.
  
Axiom proof: functional_correctness_statement.

End STRAIGHTLINE_HOARE_TRIPLE_PROOF.

