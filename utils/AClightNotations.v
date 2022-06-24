
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Clight.
Require Import CSplit.AClight.
Require Import CSplit.AClightFunc.
Require Import compcert.common.AST.


Require Import FloydSeq.proofauto.


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



(* Infix "++" := app (right associativity, at level 60).
Infix "+++" := Capp (right associativity, at level 60) : aclight_scope. *)

Notation "'GIVEN' x .. y , c " :=
  (bind_C_full_path (fun x => .. (bind_C_full_path (fun y => c)) ..)) (at level 65, x binder, y binder) : logic.

Notation "'EXGIVEN' x  '[[' ass ']]'  c " :=
  (Cexgiven _ (fun x => ass) _ (fun x => c)) (at level 65) : logic.

Notation "!!"  := semax_lemmas.Cnot.

Notation "{ x ; y ; .. ; z }" := (list_binded_cons x (list_binded_cons y .. (list_binded_cons z list_binded_nil) ..)) : list_scope.
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


    (* Require Import cprogs.reverse_prog.
    Require Import cprogs.reverse_def.

Parameter (sh:share) (p:val) (l: list val).

Definition f_reverse_hint :=
(
  (Csequence
    Cskip
    (Csequence
      Cskip
      (Csequence
        (Cset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Csequence
          (Cset _v (Etempvar _p (tptr (Tstruct _list noattr))))
          (Csequence
            (Cloop
              (Csequence
                (Cassert (
        (EX w v l1 l2,
          PROP  (l = rev l1 ++ l2)
    LOCAL (temp _w w; temp _v v)
    SEP   (listrep sh l1 w; listrep sh l2 v))%assert))
                (EXGIVEN w
                  [[((EX v l1 l2,
          PROP  (l = rev l1 ++ l2)
    LOCAL (temp _w w; temp _v v)
    SEP   (listrep sh l1 w; listrep sh l2 v))%assert)]] 
                  (EXGIVEN v
                    [[((EX l1 l2,
          PROP  (l = rev l1 ++ l2)
    LOCAL (temp _w w; temp _v v)
    SEP   (listrep sh l1 w; listrep sh l2 v))%assert)]] 
                    (EXGIVEN l1
                      [[((EX l2,
          PROP  (l = rev l1 ++ l2)
    LOCAL (temp _w w; temp _v v)
    SEP   (listrep sh l1 w; listrep sh l2 v))%assert)]] 
                      (EXGIVEN l2
                        [[((PROP  (l = rev l1 ++ l2)
    LOCAL (temp _w w; temp _v v)
    SEP   (listrep sh l1 w; listrep sh l2 v))%assert)]] 
                        (Csequence
                          (Cifthenelse (Etempvar _v (tptr (Tstruct _list noattr)))
                            Cskip
                            (Csequence Cbreak Cskip))
                          (Csequence
                            (Cassert (
          (EX t x l2',
      PROP  (l2 = x :: l2')
      LOCAL (temp _w w; temp _v v)
      SEP   (data_at sh t_struct_list (x, t) v;
              listrep sh l1 w; listrep sh l2' t))%assert))
                            (EXGIVEN t
                              [[((EX x l2',
      PROP  (l2 = x :: l2')
      LOCAL (temp _w w; temp _v v)
      SEP   (data_at sh t_struct_list (x, t) v;
              listrep sh l1 w; listrep sh l2' t))%assert)]] 
                              (EXGIVEN x
                                [[((EX l2',
      PROP  (l2 = x :: l2')
      LOCAL (temp _w w; temp _v v)
      SEP   (data_at sh t_struct_list (x, t) v;
              listrep sh l1 w; listrep sh l2' t))%assert)]] 
                                (EXGIVEN l2'
                                  [[((PROP  (l2 = x :: l2')
      LOCAL (temp _w w; temp _v v)
      SEP   (data_at sh t_struct_list (x, t) v;
              listrep sh l1 w; listrep sh l2' t))%assert)]] 
                                  (Csequence
                                    (Cset _t
                                      (Efield
                                        (Ederef
                                          (Etempvar _v (tptr (Tstruct _list noattr)))
                                          (Tstruct _list noattr)) _tail
                                        (tptr (Tstruct _list noattr))))
                                    (Csequence
                                      (Cassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _v (tptr (Tstruct _list noattr)))
                                            (Tstruct _list noattr)) _tail
                                          (tptr (Tstruct _list noattr)))
                                        (Etempvar _w (tptr (Tstruct _list noattr))))
                                      (Csequence
                                        (Cset _w
                                          (Etempvar _v (tptr (Tstruct _list noattr))))
                                        (Csequence
                                          (Cset _v
                                            (Etempvar _t (tptr (Tstruct _list noattr))))
                                          Cskip))))))))))))))
              Cskip)
            (Csequence
              (Creturn (Some (Etempvar _w (tptr (Tstruct _list noattr)))))
              Cskip))))))).



Definition f_reverse_hint_split :=
  ltac:(compute_split f_reverse_hint).

Print f_reverse_hint_split.  *)
(* Goal C_split f_append_hint = C_split f_append_hint.
unfold f_append_hint.
cbv_conns.
cbv [C_split].
unfold_split.

Definition res :=
  ltac:(cbv_conns f_append_hint).

Print res. *)
