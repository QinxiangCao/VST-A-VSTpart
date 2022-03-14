
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


Module AClight.

Definition assert := (environ -> mpred).

Inductive loop_invariant :=
  | LINull: loop_invariant
  | LISingle : assert -> loop_invariant
  | LIDouble : assert -> assert -> loop_invariant.

(** ** Statements *)

Inductive S_statement : Type :=
| Ssequence (s1: S_statement) (s2: S_statement)
| Sassert
| Sskip
| Sassign (e1:expr) (e2:expr)
| Scall  (id: option ident) (e: expr) (args: list expr)
| Sset (id: ident) (e: expr)
| Sifthenelse  (e: expr) (s1 s2: S_statement)
| Sloop (s1 s2: S_statement)
| Sbreak 
| Scontinue 
| Sreturn (e: option expr)
.

Inductive atom_statement : Type :=
| Askip : atom_statement                   (**r do nothing *)
| Aassign : expr -> expr -> atom_statement (**r assignment [lvalue = rvalue] *)
| Aset : ident -> expr -> atom_statement   (**r assignment [tempvar = rvalue] *)
| Acall: option ident -> expr 
          -> list expr -> atom_statement   (**r function call *).

Definition path:= list (expr + atom_statement) .

Inductive atom : Type :=
| mk_atom : path -> atom.

Notation atoms := (list atom). 

Inductive atom_ret : Type :=
| mk_atom_ret : path -> option expr -> atom_ret.

Notation atom_rets := (list atom_ret).

Inductive S_full_path : Type :=
| mk_S_full_path : path -> S_full_path.

Notation S_full_paths := (list S_full_path).

Inductive S_partial_pre : Type :=
| mk_S_partial_pre : path -> S_partial_pre.

Notation S_partial_pres := (list S_partial_pre).

Inductive S_partial_post : Type :=
| mk_S_partial_post : path -> S_partial_post.

Notation S_partial_posts := (list S_partial_post).

Inductive S_partial_post_ret : Type :=
| mk_S_partial_post_ret : path -> option expr -> S_partial_post_ret.

Notation S_partial_post_rets := (list S_partial_post_ret).

Check list.

Record S_result : Type := mk_S_result {
  S_pre : S_partial_pres;
  S_path : S_full_paths;
  S_post_normal : S_partial_posts;
  S_post_break : S_partial_posts;
  S_post_continue : S_partial_posts;
  S_post_return : S_partial_post_rets;
  S_atom_normal : atoms;
  S_atom_break : atoms;
  S_atom_continue : atoms;
  S_atom_return : atom_rets 
}.

Fixpoint S_split (s: S_statement) : option S_result.
Admitted.

Inductive C_statement : S_statement -> Type :=
| Csequence: forall (s1: S_statement) (s2: S_statement)
      (c1: C_statement s1) (c2: C_statement s2),
    C_statement (Ssequence s1 s2)
| Cassert: forall (a: assert),
    C_statement Sskip
| Cskip: C_statement Sskip
| Cgiven : forall (A:Type) (HA: inhabited A) (c: S_statement)
    (stm': A -> C_statement c),
    C_statement c
| Cexgiven:  forall (A:Type) (HA: inhabited A) 
    (ass: A -> assert)
    (c: S_statement)
    (a_stm': A -> C_statement c),
    C_statement (Ssequence Sassert c )
| Cassign : forall (e1:expr) (e2:expr),
    C_statement (Sassign e1 e2)
| Ccall : forall (id: option ident) (e: expr) (args: list expr),
    C_statement (Scall id e args)
| Cset : forall (id: ident) (e: expr),
    C_statement (Sset id e)
| Cifthenelse : forall (e: expr) (s1 s2: S_statement)
      (c1: C_statement s1) (c2: C_statement s2),
    C_statement (Sifthenelse e s1 s2)
| Cloop : forall (inv: loop_invariant) (s1 s2: S_statement)
      (c1: C_statement s1) (c2: C_statement s2),
    C_statement (Sloop s1 s2)
| Cbreak : C_statement (Sbreak)
| Ccontinue : C_statement (Scontinue)
| Creturn : forall (e: option expr), C_statement (Sreturn e)
.

(* TODO: is this correct? *)
Inductive list_binded_of {R : Type} {binder: R -> Type} : list R -> Type :=
| list_binded_nil : list_binded_of []
| list_binded_cons (r:R) (r': binder r) (l: list R)
                   (l':list_binded_of l) : list_binded_of (r::l).

Inductive C_full_path : S_full_path -> Type :=
| mk_C_full_path : 
    forall (pre: assert) (path: path) (post: assert),
      C_full_path (mk_S_full_path path)
| bind_C_full_path :
    forall (A: Type) (HA: inhabited A) (s: S_full_path)
           (c': A -> C_full_path s),
      C_full_path s
.

Notation C_full_paths := (@list_binded_of _ C_full_path).

Inductive C_partial_pre : S_partial_pre -> Type :=
| mk_C_partial_pre : 
    forall (path: path) (post: assert),
      C_partial_pre (mk_S_partial_pre path)
| bind_C_partial_pre :
    forall (A: Type) (HA: inhabited A) (s: S_partial_pre)
           (c': A -> C_partial_pre s),
      C_partial_pre s
.

Notation C_partial_pres := (@list_binded_of _ C_partial_pre).

Inductive C_partial_post : S_partial_post -> Type :=
| mk_C_partial_post : 
    forall (pre: assert) (path: path),
      C_partial_post (mk_S_partial_post path)
| bind_C_partial_post :
    forall (A: Type) (HA: inhabited A) (s: S_partial_post)
           (c': A -> C_partial_post s),
      C_partial_post s
.

Notation C_partial_posts := (@list_binded_of _ C_partial_post).

Inductive C_partial_post_ret : S_partial_post_ret -> Type :=
| mk_C_partial_post_ret : 
    forall (pre: assert) (path: path) (ret: option expr),
      C_partial_post_ret (mk_S_partial_post_ret path ret)
| bind_C_partial_post_ret :
    forall (A: Type) (HA: inhabited A) (s: S_partial_post_ret)
           (c': A -> C_partial_post_ret s),
      C_partial_post_ret s
.

Notation C_partial_post_rets := (@list_binded_of _ C_partial_post_ret).

Record C_result (s_res: S_result) : Type := 
  mk_C_result {
    C_pre : C_partial_pres (S_pre s_res);
    C_path : C_full_paths (S_path s_res);
    C_post_normal : C_partial_posts (S_post_normal s_res);
    C_post_break : C_partial_posts (S_post_break s_res);
    C_post_continue : C_partial_posts (S_post_continue s_res); 
    C_post_return : C_partial_post_rets (S_post_return s_res);
    C_atom_normal : atoms;
    C_atom_break : atoms;
    C_atom_continue : atoms;
    C_atom_return : atom_rets 
  }
.

Inductive option_C_result : option S_result -> Type :=
| None_C_result : option_C_result None
| Some_C_result : forall (s_res: S_result),
    option_C_result (Some s_res).

Fixpoint C_split (s: S_statement) (c: C_statement s) : option_C_result (S_split s).
Admitted.

