Require Import Ctypes Clight AClight Comment.
Require Import Coqlib Errors String List.

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Pulling local scalar variables whose address is not taken
  into temporary variables. *)

(* Require Import FSets.
Require FSetAVL.
Require Import Coqlib Ordered Errors.
Require Import AST Linking.
Require Import Ctypes Cop Clight.
Require Compopts.*)

Open Scope error_monad_scope.
Open Scope string_scope.
Open Scope list_scope.

Parameter get_binder_list : assert -> list binder * assert.

Definition add_binder_list (s: statement) (c: assert) : statement :=
  let (binder_list, dummy_assert) := get_binder_list c in
  match binder_list with
  | nil => s
  | _ =>
    let s := Ssequence (Sdummyassert dummy_assert) s in
    fold_right Sgiven s binder_list
  end.

Fixpoint loop_concat_break (s safter: statement) : statement :=
  let f :=
    fix f s :=
      match s with
      | Sbreak => Ssequence Sbreak safter
      | Sgiven binder s => Sgiven binder (f s)
      | Ssequence s1 s2 => Ssequence (f s1) (f s2)
      | Sifthenelse e s1 s2 => Sifthenelse e (f s1) (f s2)
      | Sloop inv s1 s2 => Sloop inv (f s1) (f s2)
      | Slabel lbl s => Slabel lbl (f s)
      | Sswitch e ls => Sswitch e (f' ls)
      | _ => s
      end
    with f' s :=
      match s with
      | LSnil => LSnil
      | LScons lbl s ls => LScons lbl (f s) (f' ls)
      end
    for f
  in
  f s.

Fixpoint count_break (s: statement) : res Z :=
  match s with
  | Sgiven _ s => count_break s
  | Sifthenelse _ s1 s2 =>
      do cnt1 <- count_break s1;
      do cnt2 <- count_break s2;
      OK (cnt1 + cnt2)
  | Slabel _ s => count_break s
  | _ => OK 0
  end.

Definition check_single_break (s: statement) : res unit :=
  do cnt <- count_break s;
  if cnt <=? 1
    then OK tt
    else Error (MSG "Missing postcondition for a loop with multiple exits" :: nil).

Fixpoint fold_cs (cs_list: list (comment + statement)) (acc: statement) : res statement :=
  match cs_list with
  | nil => OK acc
  | cs :: cs_list =>
    match cs with
    | inl (Inv, c) => Error (MSG "Dangling loop invariant" :: nil)
    | inl (Assert, c) =>
      match acc with
      | Sskip => fold_cs cs_list (Sassert c)
      | _ =>
        fold_cs cs_list (Ssequence (Sassert c) (add_binder_list acc c))
      end
    | inl (Given, c) => fold_cs cs_list (Sgiven c acc)
    | inl _ => Error (MSG "Funcsepc cannot appear in middle of a function" :: nil)
    | inr s =>
      match s, acc with
      | Sskip, _ => fold_cs cs_list acc
      | Sbreak, Sskip
      | Scontinue, Sskip
      | Sreturn _, Sskip
          => fold_cs cs_list s
      | Sloop inv s1 s2, Ssequence (Sassert _) _ (* If loop is followed by an assertion, use it as post condition. *)
      | Sloop inv s1 s2, Sskip (* or followed by skip *)
          => fold_cs cs_list (Ssequence s acc)
      | Sloop inv s1 s2, safter => (* If loop is not followed by an assertion or skip, check whether it only have onr break *)
          do _ <- check_single_break (Ssequence s1 s2);
          fold_cs cs_list (Ssequence (Sloop inv (loop_concat_break s1 safter) (loop_concat_break s2 safter)) Sskip)
      | _, _ => fold_cs cs_list (Ssequence s acc)
      end
    (* | _ => Error (MSG "Unimplemented" :: nil) *)
    end
  end.

Fixpoint find_inv (cs_list: list (comment + statement)) : res (loop_invariant * list (comment + statement)) :=
  match cs_list with
  | inl (Inv, inv2) :: inl (Inv, inv1) :: cs_list =>
    OK ((LIDouble inv1 inv2), cs_list)
  | inl (Inv, inv) :: cs_list =>
    OK ((LISingle inv), cs_list)
  | cs :: cs_list =>
    do (inv, cs_list) <- find_inv cs_list;
    OK (inv, cs :: cs_list)
  | _ => Error (MSG "Missing loop invariant" :: nil)
  end.

Fixpoint annotate_stmt (s: Clight.statement) : res statement :=
  let fix annotate_stmt_list (cs_list: list (comment + statement)) (s: Clight.statement) : res (list (comment + statement)) :=
    let annotate_loop (inv: loop_invariant) (s1 s2: Clight.statement) : res statement :=
      match inv with
      | LISingle inv =>
        do cs_list1 <- annotate_stmt_list nil s1;
        do cs_list2 <- annotate_stmt_list cs_list1 s2;
        do s' <- fold_cs cs_list2 Sskip;
        let s' :=
          match s' with
          | Ssequence (Sifthenelse e Sskip Sbreak) s1'
            => Ssequence (Sifthenelse e s1' Sbreak) Sskip
          | _ => s'
          end
        in
        let s'' := add_binder_list s' inv in
        OK (Sloop (LISingle inv) s'' Sskip)
      | LIDouble inv1 inv2 =>
        do s1' <- annotate_stmt s1;
        do s2' <- annotate_stmt s2;
        let s1' :=
          match s1' with
          | Ssequence (Sifthenelse e Sskip Sbreak) s1'
            => Ssequence (Sifthenelse e s1' Sbreak) Sskip
          | _ => s1'
          end
        in
        let s1'' := add_binder_list s1' inv1 in
        let s2'' := add_binder_list s2' inv2 in
        OK (Sloop (LIDouble inv1 inv2) s1'' s2'')
      end
    in
    match s with
    | Clight.Slcomment c s =>
        annotate_stmt_list (inl c :: cs_list) s
    | Clight.Srcomment s c =>
        do cs_list1 <- annotate_stmt_list cs_list s;
        OK (inl c :: cs_list1)
    | Clight.Ssequence s1 s2 =>
        do cs_list1 <- annotate_stmt_list cs_list s1;
        do cs_list2 <- annotate_stmt_list cs_list1 s2;
        OK cs_list2
    | Clight.Sloop s1 s2 =>
      do (inv, cs_list) <- find_inv cs_list;
      do s <- annotate_loop inv s1 s2;
      OK (inr s :: cs_list)
    | _ =>
      do s' <-
        match s with
        | Clight.Sifthenelse a s1 s2 =>
            do s1' <- annotate_stmt s1;
            do s2' <- annotate_stmt s2;
            OK (Sifthenelse a s1' s2')
        | Clight.Sswitch a ls =>
            do ls' <- annotate_lblstmt ls;
            OK (Sswitch a ls')
        | Clight.Slabel lbl s =>
            do s' <- annotate_stmt s;
            OK (Slabel lbl s')
        | Clight.Sskip => OK Sskip
        | Clight.Sassign a1 a2 => OK (Sassign a1 a2)
        | Clight.Sset id a => OK (Sset id a)
        | Clight.Scall optid a al => OK (Scall optid a al)
        | Clight.Sbuiltin optid ef tyargs al => OK (Sbuiltin optid ef tyargs al)
        | Clight.Sbreak => OK Sbreak
        | Clight.Scontinue => OK Scontinue
        | Clight.Sreturn opta => OK (Sreturn opta)
        | Clight.Sgoto lbl => OK (Sgoto lbl)
        | _ => Error (MSG "Internal error: invalid argument s in annotate_simple_stmt" :: nil)
        end;
      OK (inr s' :: cs_list)
    end
  in
  do cs_list <- annotate_stmt_list nil s;
  do s' <- fold_cs cs_list Sskip;
  OK s'

with annotate_lblstmt (ls: Clight.labeled_statements) : res labeled_statements :=
  match ls with
  | Clight.LSnil => OK LSnil
  | Clight.LScons c s ls1 =>
      do s' <- annotate_stmt s;
      do ls1' <- annotate_lblstmt ls1;
      OK (LScons c s' ls1')
  end.

Definition annotate_body (s: Clight.statement) : res ((binder * assert * assert) * statement) :=
  match s with
  | Clight.Slcomment (With, binder) (
      Clight.Slcomment (Require, pre) (
        Clight.Slcomment (Ensure, post) s)) =>
    do s' <- annotate_stmt s;
    OK ((binder, pre, post), s')
  | Clight.Ssequence (
      Clight.Slcomment (With, binder) (
        Clight.Slcomment (Require, pre) (
          Clight.Slcomment (Ensure, post) s1)))
      s2 =>
    do s' <- annotate_stmt (Clight.Ssequence s1 s2);
    OK ((binder, pre, post), s')
  | _ => Error (MSG "Funcspec is missing or broken" :: nil)
  end.

Definition annotate_function (f: Clight.function) : res function :=
  do (spec, body') <- annotate_body f.(Clight.fn_body);
  OK {| fn_return := f.(Clight.fn_return);
        fn_callconv := f.(Clight.fn_callconv);
        fn_params := f.(Clight.fn_params);
        fn_vars := f.(Clight.fn_vars);
        fn_temps := f.(Clight.fn_temps);
        fn_body := body';
        fn_spec := spec |}.

(** Whole-program transformation *)

Definition annotate_fundef (fd: Clight.fundef) : res fundef :=
  match fd with
  | Internal f => do tf <- annotate_function f; OK (Internal tf)
  | External ef targs tres cconv => OK (External ef targs tres cconv)
  end.

Definition annotate_program (p: Clight.program) : res program :=
  do p1 <- AST.transform_partial_program annotate_fundef p;
  OK {| prog_defs := AST.prog_defs p1;
        prog_public := AST.prog_public p1;
        prog_main := AST.prog_main p1;
        prog_types := prog_types p;
        prog_comp_env := prog_comp_env p;
        prog_comp_env_eq := prog_comp_env_eq p |}.
