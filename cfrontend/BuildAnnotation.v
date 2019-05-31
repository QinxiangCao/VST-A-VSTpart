Require Import Ctypes Clight AClight Comment.
Require Import Errors String.

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

Fixpoint fold_cs (cs_list: list (comment + statement)) (acc: statement) : res statement :=
  match cs_list with
  | nil => OK acc
  | cs :: cs_list =>
    match cs with
    | inl (Inv, c) => Error (MSG "Dangling loop invariant" :: nil)
    | inl (Assert, c) => fold_cs cs_list (Ssequence (Sassert c) acc)
    | inl (Given, c) => fold_cs cs_list (Sgiven c acc)
    | inr (Sloop _ _ s1 s2) =>
      match cs_list with
      (* If there are two invariants, put two; if there is only one invariant, use it twice. *)
      | inl (Inv, inv2) :: inl (Inv, inv1) :: cs_list =>
        fold_cs cs_list (Sloop inv1 inv2 s1 s2)
      | inl (Inv, inv) :: cs_list =>
        fold_cs cs_list (Sloop inv inv s1 s2)
      | _ => Error (MSG "Missing loop invariant" :: nil)
      end
    | inr s => fold_cs cs_list (Ssequence s acc)
    (* | _ => Error (MSG "Unimplemented" :: nil) *)
    end
  end.

Fixpoint annotate_stmt (s: Clight.statement) : res statement :=
  let fix annotate_stmt_list (cs_list: list (comment + statement)) (s: Clight.statement) : res (list (comment + statement)) :=
  match s with
  | Clight.Slcomment c s =>
      annotate_stmt_list (inl c :: cs_list) s
  | Clight.Srcomment s c =>
      do cs_list <- annotate_stmt_list cs_list s;
      OK (inl c :: cs_list)
  | Clight.Ssequence s1 s2 =>
      do cs_list <- annotate_stmt_list cs_list s1;
      do cs_list <- annotate_stmt_list cs_list s2;
      OK cs_list
  | Clight.Sloop s1 s2 =>
    do s1' <- annotate_stmt s1;
    do s2' <- annotate_stmt s2;
    match cs_list with
    (* If there are two invariants, put two; if there is only one invariant, use it twice. *)
    | inl (Inv, inv2) :: inl (Inv, inv1) :: cs_list =>
      OK (inr (Sloop inv1 inv2 s1' s2') :: cs_list)
    | inl (Inv, inv) :: cs_list =>
      OK (inr (Sloop inv inv s1' s2') :: cs_list)
    | _ => Error (MSG "Missing loop invariant" :: nil)
    end
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

Definition annotate_function (f: Clight.function) : res function :=
  do body' <- annotate_stmt f.(Clight.fn_body);
  OK {| fn_return := f.(Clight.fn_return);
        fn_callconv := f.(Clight.fn_callconv);
        fn_params := f.(Clight.fn_params);
        fn_vars := f.(Clight.fn_vars);
        fn_temps := f.(Clight.fn_temps);
        fn_body := body' |}.

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
