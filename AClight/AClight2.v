
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
  Locate mpred.
  Inductive loop_invariant :=
    | LINull: loop_invariant
    | LISingle : assert -> loop_invariant
    | LIDouble : assert -> assert -> loop_invariant.
  
  (** ** Statements *)
  

Inductive Astatement : Clight.statement -> Type :=
| Ssequence: forall (s1: Clight.statement) (s2: Clight.statement)
      (c1: Astatement s1) (c2: Astatement s2),
    Astatement (Clight.Ssequence s1 s2)
| Sassert: forall (a: assert), 
    Astatement (Clight.Sskip)
| Sskip: Astatement (Clight.Sskip)
| Sgiven:  forall (A:Type) (c: statement) (a_stm': A -> Astatement c),
    Astatement c.