Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import String.
Require Import Clight.
Require Import ClightC.

Open Scope error_monad_scope.

Parameter parse_comment : Comment.comment -> option comment.

Definition res_parse_comment (c : Comment.comment) : res comment :=
  match parse_comment c with
  | Some c => OK c
  | None => Error (MSG "invalid comment keyword" :: nil)
  end.

Fixpoint classify_stmt (s: Clight.statement) : res statement :=
  match s with
  | Clight.Slcomment c s =>
      do c <- res_parse_comment c;
      do s' <- classify_stmt s;
      OK (Slcomment c s')
  | Clight.Srcomment s c =>
      do c <- res_parse_comment c;
      do s' <- classify_stmt s;
      OK (Srcomment s' c)
  | Clight.Ssequence s1 s2 =>
      do s1' <- classify_stmt s1;
      do s2' <- classify_stmt s2;
      OK (Ssequence s1' s2')
  | Clight.Sloop s1 s2 =>
      do s1' <- classify_stmt s1;
      do s2' <- classify_stmt s2;
      OK (Sloop s1' s2')
  | Clight.Sifthenelse a s1 s2 =>
      do s1' <- classify_stmt s1;
      do s2' <- classify_stmt s2;
      OK (Sifthenelse a s1' s2')
  | Clight.Sswitch a ls =>
      do ls' <- classify_lblstmt ls;
      OK (Sswitch a ls')
  | Clight.Slabel lbl s =>
      do s' <- classify_stmt s;
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
  end
with classify_lblstmt (ls: Clight.labeled_statements) : res labeled_statements :=
  match ls with
  | Clight.LSnil => OK LSnil
  | Clight.LScons c s ls1 =>
      do s' <- classify_stmt s;
      do ls1' <- classify_lblstmt ls1;
      OK (LScons c s' ls1')
  end.


Definition classify_function (f: Clight.function) : res function :=
  do body' <- classify_stmt f.(Clight.fn_body);
  OK {| fn_return := f.(Clight.fn_return);
        fn_callconv := f.(Clight.fn_callconv);
        fn_params := f.(Clight.fn_params);
        fn_vars := f.(Clight.fn_vars);
        fn_temps := f.(Clight.fn_temps);
        fn_body := body'|}.

(** Whole-program transformation *)

Definition classify_fundef (fd: Clight.fundef) : res fundef :=
  match fd with
  | Internal f => do tf <- classify_function f; OK (Internal tf)
  | External ef targs tres cconv => OK (External ef targs tres cconv)
  end.

Definition classify_program (p: Clight.program) : res program :=
  do p1 <- AST.transform_partial_program classify_fundef p;
  OK {| prog_defs := AST.prog_defs p1;
        prog_public := AST.prog_public p1;
        prog_main := AST.prog_main p1;
        prog_types := prog_types p;
        prog_comp_env := prog_comp_env p;
        prog_comp_env_eq := prog_comp_env_eq p |}.
