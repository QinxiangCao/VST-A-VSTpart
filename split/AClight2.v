
(** The Clight language: a simplified version of Compcert C where all
  expressions are pure and assignments and function calls are
  statements, not expressions. *)

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
Require Import Clight.
Require Export VST.floyd.proofauto.
  
Definition assert := (environ -> mpred).

Inductive loop_invariant :=
  | LINull: loop_invariant
  | LISingle : assert -> loop_invariant
  | LIDouble : assert -> assert -> loop_invariant.

(** ** Statements *)
  

(* (A -> list n result)  -> list n result

add refinement to the type of the split ressult
so that adding bind can be det

*)


Inductive split_statement : Type :=
  | SSassert : split_statement
  | SSatom : split_statement                   (**r do nothing *)
  | SSsequence : split_statement -> split_statement -> split_statement  (**r sequence *)
  | SSifthenelse : split_statement -> split_statement -> split_statement (**r conditional *)
  | SSloop: split_statement -> split_statement -> split_statement (**r infinite loop *)
  | SSbreak : split_statement                      (**r [break] statement *)
  | SScontinue : split_statement                   (**r [continue] statement *)
  | SSreturn : split_statement      (**r [return] statement *)
.




Inductive statement : Clight.statement -> split_statement -> Type :=
| Ssequence: forall (s1: Clight.statement) (s2: Clight.statement)
      (ss1: split_statement) (ss2: split_statement)
      (c1: statement s1 ss1) (c2: statement s2 ss2),
    statement (Clight.Ssequence s1 s2) (SSsequence ss1 ss2)
| Sassert: forall (a: assert),
    statement (Clight.Sskip) SSassert
| Sskip: statement (Clight.Sskip) SSatom
| Sgiven : forall (A:Type) (a:A) (c: Clight.statement) (ss: split_statement)
    (a_stm': A -> statement c ss),
    statement c ss.

(* | Sexgiven:  forall (A:Type) (a:A) (ass: A -> assert)  (c: Clight.statement) (a_stm': A -> statement c),
    statement c
| Sgiven:  forall (A:Type) (a:A) (c: Clight.statement) (a_stm': A -> statement c),
    statement c
| Sassign : forall (e1:expr) (e2:expr),
    statement (Clight.Sassign e1 e2)
| Scall : forall (id: option ident) (e: expr) (args: list expr),
    statement (Clight.Scall id e args)
| Sset : forall (id: ident) (e: expr),
    statement (Clight.Sset id e)
| Sifthenelse : forall (e: expr) (s1 s2: Clight.statement)
      (c1: statement s1) (c2: statement s2),
    statement (Clight.Sifthenelse e s1 s2)
| Sloop : forall (inv: loop_invariant) (s1 s2: Clight.statement)
      (c1: statement s1) (c2: statement s2),
    statement (Clight.Sloop s1 s2)
| Sbreak : statement (Clight.Sbreak)
| Scontinue : statement (Clight.Scontinue)
| Sreturn : forall (e: option expr), statement (Clight.Sreturn e)
. *)

