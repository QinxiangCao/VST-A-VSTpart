
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



Inductive S_result : Type := 
| mk_S_result 
  (S_pre : S_partial_pres)
  (S_path : S_full_paths)
  (S_post_normal : S_partial_posts)
  (S_post_break : S_partial_posts)
  (S_post_continue : S_partial_posts)
  (S_post_return : S_partial_post_rets)
  (S_atom_normal : atoms)
  (S_atom_break : atoms)
  (S_atom_continue : atoms)
  (S_atom_return : atom_rets)
| no_S_result
. 



(* Inductive S_result : Type :=
| mk_S_result
   (S_pre : S_partial_pres)
   (S_path : S_full_paths)
   (S_post_normal : S_partial_posts)
   (S_post_break : S_partial_posts)
   (S_post_continue : S_partial_posts)
   (S_post_return : S_partial_post_rets)
   (S_atom_normal : atoms)
   (S_atom_break : atoms)
   (S_atom_continue : atoms)
   (S_atom_return : atom_rets)
. *)

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
    (* C_statement (Ssequence Sassert c ) *)
    C_statement c
    (* TODO: to be refined *)
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


Parameter atoms_conn_returns : atoms -> atom_rets -> atom_rets.
Parameter atoms_conn_atoms : atoms -> atoms -> atoms.
Parameter atoms_conn_Spres : atoms -> S_partial_pres -> S_partial_pres.
Parameter Sposts_conn_atoms : S_partial_posts -> atoms -> S_partial_posts.
Parameter Sposts_conn_returns : S_partial_posts -> atom_rets -> S_partial_post_rets.
Parameter Sposts_conn_Spres : S_partial_posts -> S_partial_pres -> S_full_paths.

Fixpoint atoms_conn_Cpres 
  (atoms: atoms)
  {Spres: S_partial_pres}
  (Cpres: C_partial_pres Spres) 
  : (C_partial_pres (atoms_conn_Spres atoms Spres)).
Admitted.


Fixpoint Cposts_conn_atoms 
  {s_posts : S_partial_posts}
  (c_posts : C_partial_posts s_posts) 
  (atoms: atoms)
  : (C_partial_posts (Sposts_conn_atoms s_posts atoms)).
Admitted.

Fixpoint Cposts_conn_returns
  {s_posts : S_partial_posts}
  (c_posts : C_partial_posts s_posts) 
  (atoms: atom_rets)
  : (C_partial_post_rets (Sposts_conn_returns s_posts atoms)).
Admitted.

Fixpoint Cposts_conn_Cpres
  {s_posts : S_partial_posts}
  (c_posts : C_partial_posts s_posts)
  {s_pres: S_partial_pres}
  (c_pres: C_partial_pres s_pres)
  : (C_full_paths (Sposts_conn_Spres s_posts s_pres)).
Admitted.



Definition S_result_sequence res1 res2 := 
  match res1 with
  | mk_S_result s_pre1 s_path1 
        s_post_normal1 s_post_break1 s_post_continue1 s_post_return1
        s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1 =>
    match res2 with
    | mk_S_result s_pre2 s_path2 
          s_post_normal2 s_post_break2 s_post_continue2 s_post_return2
          s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2 =>
      mk_S_result 
      (* S_pre *)
        (s_pre1 ++ atoms_conn_Spres s_atom_normal1 s_pre2)
      (* S_path *)
        (s_path1 ++ s_path2 ++ 
          Sposts_conn_Spres s_post_normal1 s_pre2)
      (* S_post_normal *)
        (s_post_normal2 ++ 
          Sposts_conn_atoms s_post_normal1 s_atom_normal2)
      (* S_post_break *)
        (s_post_break1 ++ s_post_break2 ++ 
          Sposts_conn_atoms s_post_normal1 s_atom_break2)
      (* S_post_continue *)
        (s_post_continue1 ++ s_post_continue2 ++ 
          Sposts_conn_atoms s_post_normal1 s_atom_continue2)
      (* S_post_return *)
        (s_post_return1 ++ s_post_return2 ++ 
          Sposts_conn_returns s_post_normal1 s_atom_return2)
      (* S_atom_normal *)
        (atoms_conn_atoms s_atom_normal1 s_atom_normal2)
      (* S_atom_break *)
        (s_atom_break1 ++
          atoms_conn_atoms s_atom_normal1 s_atom_break2)
      (* S_atom_continue *)
        (s_atom_continue1 ++
          atoms_conn_atoms s_atom_normal1 s_atom_continue2)
      (* S_atom_return *)
        (s_atom_return1 ++
          atoms_conn_returns s_atom_normal1 s_atom_return2)
    | no_S_result => no_S_result
    end
  | no_S_result => no_S_result
  end.

Inductive C_result : S_result -> Type := 
| mk_C_result : forall 
    (S_pre : S_partial_pres)
    (C_pre : C_partial_pres (S_pre))
    (S_path : S_full_paths)
    (C_path : C_full_paths (S_path))
    (S_post_normal : S_partial_posts)
    (C_post_normal : C_partial_posts (S_post_normal))
    (S_post_break : S_partial_posts)
    (C_post_break : C_partial_posts (S_post_break))
    (S_post_continue : S_partial_posts)
    (C_post_continue : C_partial_posts (S_post_continue))
    (S_post_return : S_partial_post_rets)
    (C_post_return : C_partial_post_rets (S_post_return))
    (S_atom_normal : atoms)
    (S_atom_break : atoms)
    (S_atom_continue : atoms)
    (S_atom_return : atom_rets),
      C_result (mk_S_result 
                  S_pre S_path 
                  S_post_normal S_post_break 
                  S_post_continue S_post_return
                  S_atom_normal S_atom_break 
                  S_atom_continue S_atom_return)
| no_C_result : C_result no_S_result.

Definition option_map2 {A B C:Type} (f:A->B->C) 
  (o1 : option A) (o2 : option B) : option C :=
  match o1, o2 with
    | Some a, Some b => @Some C (f a b)
    | _, _ => @None C
  end.

Parameter default_S_result : S_result.

Fixpoint S_split (s: S_statement) : S_result :=
  match s with
  | Ssequence s1 s2 =>
      let res1 := S_split s1 in
      let res2 := S_split s2 in
      S_result_sequence res1 res2
  | _ => default_S_result
  end.




Definition hd_of {R A:Type} {binder: R -> Type} (x: R) (xs: list R) 
  (res' : A -> @list_binded_of R binder (x::xs)) : A -> binder x :=
  fun a => 
    match (res' a) with
    | list_binded_cons x x' xs xsb => x'
    end.


Definition tl_of {R A:Type} {binder: R -> Type} (x: R) (xs: list R)
  (res' : A -> @list_binded_of R binder (x::xs)) : A -> list_binded_of xs :=
  fun a => 
    match (res' a) with
    | list_binded_cons x x' xs xsb => xsb
    end.

Section Cres_proj.


Context {s_pre : S_partial_pres}.
Context {s_path : S_full_paths}.
Context {s_post_normal : S_partial_posts}.
Context {s_post_break : S_partial_posts}.
Context {s_post_continue : S_partial_posts}.
Context {s_post_return : S_partial_post_rets}.
Context {s_atom_normal : atoms}.
Context {s_atom_break : atoms}.
Context {s_atom_continue : atoms}.
Context {s_atom_return : atom_rets}.

Notation s_res :=
  (mk_S_result s_pre s_path 
    s_post_normal s_post_break s_post_continue s_post_return
    s_atom_normal s_atom_break s_atom_continue s_atom_return).


Definition C_result_proj_C_pre (A : Type) (c_res: A -> C_result s_res) : A -> C_partial_pres s_pre :=
  fun a =>
    match (c_res a) with
    | mk_C_result _ C_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        C_pre
    end.

Definition C_result_proj_C_post_normal (A : Type) (c_res: A -> C_result s_res) : A -> C_partial_posts s_post_normal :=
  fun a =>
    match (c_res a) 
    with
    | mk_C_result _ _ _ _ _ C_post_normal _ _ _ _ _ _ _ _ _ _ =>
    C_post_normal
    end.


Definition C_result_proj_C_post_break (A : Type) (c_res: A -> C_result s_res) : A -> C_partial_posts (s_post_break).
Admitted.

Definition C_result_proj_C_post_continue (A : Type) (c_res: A -> C_result s_res) : A -> C_partial_posts (s_post_continue).
Admitted.

Definition C_result_proj_C_post_return (A : Type) (c_res: A -> C_result s_res) : A -> C_partial_post_rets (s_post_return).
Admitted.

Definition C_result_proj_C_path (A : Type) (c_res: A -> C_result s_res) : A -> C_full_paths (s_path).
Admitted.

Fixpoint flatten_binds {R A:Type} {binder: R -> Type} 
(HA: inhabited A)
(binder_intro : forall (r : R),
    (A -> binder r) -> binder r)
(res: list R):
(A -> @list_binded_of R binder res) -> list_binded_of res :=
match res with
| nil => fun res' => (list_binded_nil)
| x::xs =>
    fun res' =>
    list_binded_cons
      x (binder_intro x (hd_of x xs res'))
      xs (flatten_binds HA binder_intro xs (tl_of x xs res'))
end.

End Cres_proj.

Definition flatten_partial_pres_binds {A:Type}
  (HA: inhabited A)
  (s_pres: S_partial_pres)
  (c_pres': A -> C_partial_pres s_pres)
  : C_partial_pres s_pres :=
  @flatten_binds S_partial_pre A C_partial_pre HA (bind_C_partial_pre A HA) s_pres c_pres'.



Definition flatten_partial_posts_binds {A:Type}
  (HA: inhabited A)
  (s_posts: S_partial_posts)
  (c_posts': A -> C_partial_posts s_posts)
  : C_partial_posts s_posts :=
  flatten_binds HA (bind_C_partial_post A HA) s_posts c_posts'.


Definition flatten_partial_post_rets_binds {A:Type}
  (HA: inhabited A)
  (s_posts: S_partial_post_rets)
  (c_posts': A -> C_partial_post_rets s_posts)
  : C_partial_post_rets s_posts :=
  flatten_binds HA (bind_C_partial_post_ret A HA) s_posts c_posts'.

Definition flatten_full_paths_binds {A:Type}
  (HA: inhabited A)
  (s_paths: S_full_paths)
  (c_paths': A -> C_full_paths s_paths)
  : C_full_paths s_paths :=
  flatten_binds HA (bind_C_full_path A HA) s_paths c_paths'.

Definition C_result_binder_intro (s_res : S_result) (A : Type) (HA: inhabited A) :
(A -> C_result s_res) ->
C_result s_res
(* C_result s_res *)
:= 
match s_res with
| mk_S_result S_pre S_path S_post_normal S_post_break S_post_continue S_post_return S_atom_normal S_atom_break S_atom_continue S_atom_return =>
fun c_res' =>
let c_pre := C_result_proj_C_pre A c_res' in
let c_pre := flatten_partial_pres_binds HA (S_pre) c_pre in
let c_post_normal := C_result_proj_C_post_normal A c_res' in
let c_post_normal := flatten_partial_posts_binds HA (S_post_normal) c_post_normal in
let c_post_break := C_result_proj_C_post_break A c_res' in
let c_post_break := flatten_partial_posts_binds HA (S_post_break) c_post_break in
let c_post_continue := C_result_proj_C_post_continue A c_res' in
let c_post_continue := flatten_partial_posts_binds HA (S_post_continue) c_post_continue in
let c_post_return := C_result_proj_C_post_return A c_res' in
let c_post_return := flatten_partial_post_rets_binds HA (S_post_return) c_post_return in
let c_path := C_result_proj_C_path A c_res' in
let c_path := flatten_full_paths_binds HA (S_path) c_path in
mk_C_result 
  (S_pre) c_pre
  (S_path) c_path
  (S_post_normal) c_post_normal
  (S_post_break) c_post_break
  (S_post_continue) c_post_continue
  (S_post_return) c_post_return
  (S_atom_normal)
  (S_atom_break)
  (S_atom_continue)
  (S_atom_return)
| no_S_result => fun _ => no_C_result
end.


Definition Capp {A:Type} {binder: A -> Type} 
  {sl1: list A} (cl1 : @list_binded_of A binder sl1)
  {sl2: list A} (cl2 : @list_binded_of A binder sl2)
  : @list_binded_of A binder (sl1 ++ sl2).
Admitted.


Infix "+++" := Capp (right associativity, at level 60).

Check mk_C_result.

Parameter default_C_result : C_result default_S_result.


Program Definition C_split_sequence 
(s1 s2 : S_statement)
(* (c1: C_statement s1) (c2: C_statement s2) *)
: C_result (S_split s1) ->
  C_result (S_split s2) ->
  C_result (S_split (Ssequence s1 s2)) :=
match S_split s1 with
| mk_S_result s_pre1 s_path1 
    s_post_normal1 s_post_break1 s_post_continue1 s_post_return1
    s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1 =>
  match S_split s2 with
  | mk_S_result s_pre2 s_path2 
        s_post_normal2 s_post_break2 s_post_continue2 s_post_return2
        s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2 =>
    fun c_res1 c_res2 =>
    match c_res1 with
    | no_C_result => default_C_result
    | mk_C_result s_pre1 c_pre1 _ c_path1 _ c_post_normal1 
        _ c_post_break1 _ c_post_continue1 _ c_post_return1 _ _ _ _ =>
    match c_res2 with    
    | no_C_result => no_C_result
    | mk_C_result _ c_pre2 _ c_path2 _ c_post_normal2 
        _ c_post_break2 _ c_post_continue2 _ c_post_return2 _ _ _ _ =>
      mk_C_result
      (* S_pre *)
        (s_pre1 ++ atoms_conn_Spres s_atom_normal1 s_pre2)
      (* C_pre *)
        (c_pre1 +++ atoms_conn_Cpres s_atom_normal1 c_pre2)
      (* S_path *)
        (s_path1 ++ s_path2 ++ 
          Sposts_conn_Spres s_post_normal1 s_pre2)
      (* C_path *)
        (c_path1 +++ c_path2 +++ 
          Cposts_conn_Cpres c_post_normal1 c_pre2)
      (* S_post_normal *)
        (s_post_normal2 ++ 
          Sposts_conn_atoms s_post_normal1 s_atom_normal2)
      (* C_post_normal *)
        (c_post_normal2 +++ 
          Cposts_conn_atoms c_post_normal1 s_atom_normal2)
      (* S_post_break *)
        (s_post_break1 ++ s_post_break2 ++ 
          Sposts_conn_atoms s_post_normal1 s_atom_break2)
      (* C_post_break *)
        (c_post_break1 +++ c_post_break2 +++
          Cposts_conn_atoms c_post_normal1 s_atom_break2)
      (* S_post_continue *)
        (s_post_continue1 ++ s_post_continue2 ++ 
          Sposts_conn_atoms s_post_normal1 s_atom_continue2)
      (* C_post_continue *)
        (c_post_continue1 +++ c_post_continue2 +++ 
          Cposts_conn_atoms c_post_normal1 s_atom_continue2)
      (* S_post_return *)
        (s_post_return1 ++ s_post_return2 ++ 
          Sposts_conn_returns s_post_normal1 s_atom_return2)
      (* C_post_return *)
        (c_post_return1 +++ c_post_return2 +++ 
          Cposts_conn_returns c_post_normal1 s_atom_return2)
      (* S_atom_normal *)
        (atoms_conn_atoms s_atom_normal1 s_atom_normal2)
      (* S_atom_break *)
        (s_atom_break1 ++
          atoms_conn_atoms s_atom_normal1 s_atom_break2)
      (* S_atom_continue *)
        (s_atom_continue1 ++
          atoms_conn_atoms s_atom_normal1 s_atom_continue2)
      (* S_atom_return *)
        (s_atom_return1 ++
          atoms_conn_returns s_atom_normal1 s_atom_return2)
    end
    end
  | no_S_result => fun _ _ => no_C_result
  end
| no_S_result => fun _ _ => no_C_result
end.

Section Cres_2comb.

(* Context {s_pre1 : S_partial_pres}.
Context {s_path1 : S_full_paths}.
Context {s_post_normal1 : S_partial_posts}.
Context {s_post_break1 : S_partial_posts}.
Context {s_post_continue1 : S_partial_posts}.
Context {s_post_return1 : S_partial_post_rets}.
Context {s_atom_normal1 : atoms}.
Context {s_atom_break1 : atoms}.
Context {s_atom_continue1 : atoms}.
Context {s_atom_return1 : atom_rets}.

Context {s_pre2 : S_partial_pres}.
Context {s_path2 : S_full_paths}.
Context {s_post_normal2 : S_partial_posts}.
Context {s_post_break2 : S_partial_posts}.
Context {s_post_continue2 : S_partial_posts}.
Context {s_post_return2 : S_partial_post_rets}.
Context {s_atom_normal2 : atoms}.
Context {s_atom_break2 : atoms}.
Context {s_atom_continue2 : atoms}.
Context {s_atom_return2 : atom_rets}.

Notation s1 := (mk_S_result s_pre1 s_path1 
  s_post_normal1 s_post_break1 s_post_continue1 s_post_return1
  s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1).

Notation s2 := (mk_S_result s_pre2 s_path2 
  s_post_normal2 s_post_break2 s_post_continue2 s_post_return2
  s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2). *)

Definition C_split_sequence'
(s1 s2 : S_statement)
: C_result (S_split s1) ->
  C_result (S_split s2) ->
  C_result (S_split (Ssequence s1 s2)) :=
fun c_res1 c_res2 =>
  match 
    c_res1 in C_result s_res1,
    c_res2 in C_result s_res2
    return (
      match s_res1, s_res2 with
      | mk_S_result s_pre1 s_path1 
          s_post_normal1 s_post_break1 s_post_continue1 s_post_return1
          s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1, 
        mk_S_result s_pre2 s_path2 
          s_post_normal2 s_post_break2 s_post_continue2 s_post_return2
          s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2 =>
        
    
    ) with
    | no_C_result, _ => no_C_result
    | _, no_C_result => no_C_result
    | mk_C_result _ c_pre1 _ c_path1 _ c_post_normal1 
    _ c_post_break1 _ c_post_continue1 _ c_post_return1 _ _ _ _ 
     , mk_C_result _ c_pre2 _ c_path2 _ c_post_normal2 
        _ c_post_break2 _ c_post_continue2 _ c_post_return2 _ _ _ _ =>
      mk_C_result
      (* S_pre *)
        (s_pre1 ++ atoms_conn_Spres s_atom_normal1 s_pre2)
      (* C_pre *)
        (c_pre1 +++ atoms_conn_Cpres s_atom_normal1 c_pre2)
      (* S_path *)
        (s_path1 ++ s_path2 ++ 
          Sposts_conn_Spres s_post_normal1 s_pre2)
      (* C_path *)
        (c_path1 +++ c_path2 +++ 
          Cposts_conn_Cpres c_post_normal1 c_pre2)
      (* S_post_normal *)
        (s_post_normal2 ++ 
          Sposts_conn_atoms s_post_normal1 s_atom_normal2)
      (* C_post_normal *)
        (c_post_normal2 +++ 
          Cposts_conn_atoms c_post_normal1 s_atom_normal2)
      (* S_post_break *)
        (s_post_break1 ++ s_post_break2 ++ 
          Sposts_conn_atoms s_post_normal1 s_atom_break2)
      (* C_post_break *)
        (c_post_break1 +++ c_post_break2 +++
          Cposts_conn_atoms c_post_normal1 s_atom_break2)
      (* S_post_continue *)
        (s_post_continue1 ++ s_post_continue2 ++ 
          Sposts_conn_atoms s_post_normal1 s_atom_continue2)
      (* C_post_continue *)
        (c_post_continue1 +++ c_post_continue2 +++ 
          Cposts_conn_atoms c_post_normal1 s_atom_continue2)
      (* S_post_return *)
        (s_post_return1 ++ s_post_return2 ++ 
          Sposts_conn_returns s_post_normal1 s_atom_return2)
      (* C_post_return *)
        (c_post_return1 +++ c_post_return2 +++ 
          Cposts_conn_returns c_post_normal1 s_atom_return2)
      (* S_atom_normal *)
        (atoms_conn_atoms s_atom_normal1 s_atom_normal2)
      (* S_atom_break *)
        (s_atom_break1 ++
          atoms_conn_atoms s_atom_normal1 s_atom_break2)
      (* S_atom_continue *)
        (s_atom_continue1 ++
          atoms_conn_atoms s_atom_normal1 s_atom_continue2)
      (* S_atom_return *)
        (s_atom_return1 ++
          atoms_conn_returns s_atom_normal1 s_atom_return2)
    end
  | no_S_result => fun _ _ => no_C_result
  end
| no_S_result => fun _ _ => no_C_result
end.


End Cres_2comb.

Definition C_split_sequence 
(s1 s2 : S_statement)
(* (c1: C_statement s1) (c2: C_statement s2) *)
(c_res1: C_result (S_split s1))
(c_res2: C_result (S_split s2)) ->
  C_result (S_split (Ssequence s1 s2)) :=
match c_res1 as c_res1' 
  in C_result (S_split s1')
  return (C_result (S_split s2) =>

  ) with


match S_split s1 with
| mk_S_result s_pre1 s_path1 
    s_post_normal1 s_post_break1 s_post_continue1 s_post_return1
    s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1 =>
  match S_split s2 with
  | mk_S_result s_pre2 s_path2 
        s_post_normal2 s_post_break2 s_post_continue2 s_post_return2
        s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2 =>
    fun c_res1 c_res2 =>
    match c_res1 with
    | no_C_result => default_C_result
    | mk_C_result _ c_pre1 _ c_path1 _ c_post_normal1 
        _ c_post_break1 _ c_post_continue1 _ c_post_return1 _ _ _ _ =>
    match c_res2 with    
    | no_C_result => no_C_result
    | mk_C_result _ c_pre2 _ c_path2 _ c_post_normal2 
        _ c_post_break2 _ c_post_continue2 _ c_post_return2 _ _ _ _ =>
      mk_C_result
      (* S_pre *)
        (s_pre1 ++ atoms_conn_Spres s_atom_normal1 s_pre2)
      (* C_pre *)
        (c_pre1 +++ atoms_conn_Cpres s_atom_normal1 c_pre2)
      (* S_path *)
        (s_path1 ++ s_path2 ++ 
          Sposts_conn_Spres s_post_normal1 s_pre2)
      (* C_path *)
        (c_path1 +++ c_path2 +++ 
          Cposts_conn_Cpres c_post_normal1 c_pre2)
      (* S_post_normal *)
        (s_post_normal2 ++ 
          Sposts_conn_atoms s_post_normal1 s_atom_normal2)
      (* C_post_normal *)
        (c_post_normal2 +++ 
          Cposts_conn_atoms c_post_normal1 s_atom_normal2)
      (* S_post_break *)
        (s_post_break1 ++ s_post_break2 ++ 
          Sposts_conn_atoms s_post_normal1 s_atom_break2)
      (* C_post_break *)
        (c_post_break1 +++ c_post_break2 +++
          Cposts_conn_atoms c_post_normal1 s_atom_break2)
      (* S_post_continue *)
        (s_post_continue1 ++ s_post_continue2 ++ 
          Sposts_conn_atoms s_post_normal1 s_atom_continue2)
      (* C_post_continue *)
        (c_post_continue1 +++ c_post_continue2 +++ 
          Cposts_conn_atoms c_post_normal1 s_atom_continue2)
      (* S_post_return *)
        (s_post_return1 ++ s_post_return2 ++ 
          Sposts_conn_returns s_post_normal1 s_atom_return2)
      (* C_post_return *)
        (c_post_return1 +++ c_post_return2 +++ 
          Cposts_conn_returns c_post_normal1 s_atom_return2)
      (* S_atom_normal *)
        (atoms_conn_atoms s_atom_normal1 s_atom_normal2)
      (* S_atom_break *)
        (s_atom_break1 ++
          atoms_conn_atoms s_atom_normal1 s_atom_break2)
      (* S_atom_continue *)
        (s_atom_continue1 ++
          atoms_conn_atoms s_atom_normal1 s_atom_continue2)
      (* S_atom_return *)
        (s_atom_return1 ++
          atoms_conn_returns s_atom_normal1 s_atom_return2)
    end
    end
  | no_S_result => fun _ _ => no_C_result
  end
| no_S_result => fun _ _ => no_C_result
end.
    
    (S_pre : S_partial_pres)
    (C_pre : C_partial_pres (S_pre))
    (S_path : S_full_paths)
    (C_path : C_full_paths (S_path))
    (S_post_normal : S_partial_posts)
    (C_post_normal : C_partial_posts (S_post_normal))
    (S_post_break : S_partial_posts)
    (C_post_break : C_partial_posts (S_post_break))
    (S_post_continue : S_partial_posts)
    (C_post_continue : C_partial_posts (S_post_continue))
    (S_post_return : S_partial_post_rets)
    (C_post_return : C_partial_post_rets (S_post_return))
    (S_atom_normal : atoms)
    (S_atom_break : atoms)
    (S_atom_continue : atoms)
    (S_atom_return : atom_rets)





    mk_S_result 
      (s_pre1 ++ atoms_conn_Spres s_atom_normal1 s_pre2)
      (s_path1 ++ s_path2 ++ 
        Sposts_conn_Spres s_post_normal1 s_pre2)
      (s_post_normal2 ++ 
        Sposts_conn_atoms s_post_normal1 s_atom_normal2)
      (s_post_break1 ++ s_post_break2 ++ 
        Sposts_conn_atoms s_post_normal1 s_atom_break2)
      (s_post_continue1 ++ s_post_continue2 ++ 
        Sposts_conn_atoms s_post_normal1 s_atom_continue2)
      (s_post_return1 ++ s_post_return2 ++ 
        Sposts_conn_returns s_post_normal1 s_atom_return2)
      (atoms_conn_atoms s_atom_normal1 s_atom_normal2)
      (s_atom_break1 ++
        atoms_conn_atoms s_atom_normal1 s_atom_break2)
      (s_atom_continue1 ++
        atoms_conn_atoms s_atom_normal1 s_atom_continue2)
      (s_atom_return1 ++
        atoms_conn_returns s_atom_normal1 s_atom_return2)
  | no_S_result => no_S_result
  end
| no_S_result => no_S_result
end.



Admitted.

Fixpoint C_split (s: S_statement) (c: C_statement s) : C_result (S_split s) :=
match c as c0 in C_statement s0
  return C_result (S_split s0)
with
| Csequence s1 s2 c1 c2 =>
    C_split_sequence s1 s2 (C_split s1 c1) (C_split s2 c2) c1 c2
| Cassert a => 
    default_C_result
| Cskip => 
    default_C_result
| Cgiven A HA c a_stm' =>
    C_result_binder_intro (S_split c) A HA (fun a =>  C_split c (a_stm' a))
| Cexgiven A HA ass c a_stm' =>
    C_result_binder_intro (S_split c) A HA (fun a =>  C_split c (a_stm' a))
| Cassign e1 e2 =>
    default_C_result
| Ccall id e args =>
    default_C_result
| Cset id e =>
    default_C_result
| Cifthenelse e1 s1 s2 c1 c2 =>
    default_C_result
| Cloop inv s1 s2 c1 c2 =>
    default_C_result
| Cbreak =>
    default_C_result
| Ccontinue =>
    default_C_result
| Creturn e =>
    default_C_result
end.



(* Legacy rules



  split_seq: forall stm1 stm2 res1 res2,
    path_split stm1 res1 ->
    path_split stm2 res2 ->
    ((all_basic (S_pre res2) = true) (* __ ;; basic *)  \/
    ((* basic ;; bind*)
      (all_basic(S_post_normal res1) = true) /\
      (all_empty_path (S_post_normal res1)=true) /\
      (all_empty_atom (S_atom_normal res1)=true)
    )) ->
    path_split (stm1;;stm2)
      ({|
        S_pre := S_pre res1 ++ atoms_conn_pres (S_atom_normal res1) (S_pre res2);
        S_path := S_path res1 ++ S_path res2 ++ posts_conn_pres (S_post_normal res1) (S_pre res2);
        S_post_normal := S_post_normal res2 ++ posts_conn_atoms (S_post_normal res1) (S_atom_normal res2);
        S_post_continue := S_post_continue res1 ++ S_post_continue res2
                          ++ posts_conn_atoms (S_post_normal res1) (S_atom_continue res2);
        S_post_break := S_post_break res1 ++ S_post_break res2
                          ++ posts_conn_atoms (S_post_normal res1) (S_atom_break  res2);
        S_post_return := S_post_return res1 ++ S_post_return res2
                          ++ posts_conn_returns (S_post_normal res1) (S_atom_return res2);
        S_atom_normal := atoms_conn_atoms (S_atom_normal res1) (S_atom_normal res2);
        S_atom_return := S_atom_return res1 ++ atoms_conn_returns (S_atom_normal res1) (S_atom_return res2);
        S_atom_break  := S_atom_break  res1 ++ atoms_conn_atoms (S_atom_normal res1) (S_atom_break  res2);
        S_atom_continue := S_atom_continue res1 ++ atoms_conn_atoms (S_atom_normal res1) (S_atom_continue res2);
        |})
| split_base: forall stm res,
    basic_split stm res ->
    path_split stm res
| split_if:
   forall a stm1 stm2 res1 res2,
    path_split stm1 res1 ->
    path_split stm2 res2 ->
    path_split (Sifthenelse a stm1 stm2)
    {|
      S_pre := add_exp_to_pres a (S_pre res1) ++ add_exp_to_pres (Cnot a) (S_pre res2);
      S_path := S_path res1 ++ S_path res2;
      S_post_normal := S_post_normal res1 ++ S_post_normal res2;
      S_post_continue := S_post_continue res1 ++ S_post_continue res2;
      S_post_return := S_post_return res1 ++ S_post_return res2;
      S_post_break := S_post_break res1 ++ S_post_break res2;
      S_atom_normal := add_exp_to_atoms a (S_atom_normal res1) 
                    ++ add_exp_to_atoms (Cnot a) (S_atom_normal res2);
      S_atom_break  := add_exp_to_atoms a (S_atom_break  res1) 
                    ++ add_exp_to_atoms (Cnot a) (S_atom_break  res2);
      S_atom_return := add_exp_to_return_atoms a (S_atom_return res1) 
                    ++ add_exp_to_return_atoms (Cnot a) (S_atom_return res2);
      S_atom_continue := add_exp_to_atoms a (S_atom_continue res1) 
                    ++ add_exp_to_atoms (Cnot a) (S_atom_continue res2);
    |}
| Split_loop_double: forall inv1 inv2 c1 c2 res1 res2 
  (Econt_atom: S_atom_continue res2 = [])
  (Econt_post: S_post_continue res2 = [])
  (* (Ebasic_normal1: all_basic (S_post_normal res1)= true)
  (Ebasic_continue1: all_basic (S_post_continue res1)= true)
  (Ebasic_pre2: all_basic (S_pre res2)= true) *) ,
    path_split c1 res1 ->
    path_split c2 res2 ->
    path_split (Sloop (LIDouble inv1 inv2) c1 c2) {|
      S_pre := [(Basic_partial inv1,nil)];
      S_path := 
        posts_conn_pres [(Basic_partial inv1, nil)] (S_pre res1) ++
        posts_conn_pres [(Basic_partial inv1, nil)]
          (atoms_conn_pres (S_atom_normal res1) [(Basic_partial inv2, nil)]) ++
        posts_conn_pres [(Basic_partial inv1, nil)]
          (atoms_conn_pres (S_atom_continue res1) [(Basic_partial inv2, nil)]) ++
        posts_conn_pres (S_post_normal res1) [(Basic_partial inv2, nil)] ++
        posts_conn_pres (S_post_continue res1) [(Basic_partial inv2, nil)] ++
        posts_conn_pres [(Basic_partial inv2, nil)] (S_pre res2) ++
        posts_conn_pres [(Basic_partial inv2, nil)]
          (atoms_conn_pres (S_atom_normal res2) [(Basic_partial inv1, nil)]) ++
        posts_conn_pres (S_post_normal res2) [(Basic_partial inv1, nil)] ++
        posts_conn_pres (S_post_continue res2) [(Basic_partial inv1, nil)]++
        S_path res1 ++ S_path res2;
      S_post_normal :=
        S_post_break res1 ++ S_post_break res2 ++
        posts_conn_atoms [(Basic_partial inv1, nil)] (S_atom_break  res1) ++
        posts_conn_atoms [(Basic_partial inv2, nil)] (S_atom_break  res2);
      S_post_continue := nil;
      S_post_break := nil;
      S_post_return :=
        (S_post_return res1) ++ (S_post_return res2) ++
        posts_conn_returns [(Basic_partial inv1, nil)] (S_atom_return res1) ++
        posts_conn_returns [(Basic_partial inv2, nil)] (S_atom_return res2) ;
      S_atom_normal := nil;
      S_atom_break  := nil;
      S_atom_continue := nil;
      S_atom_return := nil
          (* no continue condition in c2 *)
    |}
(* | split_loop_single_skip: forall inv c1 c1' c2 c2' res,
    AClight_to_Clight c1 c1' ->
    AClight_to_Clight c2 c2' ->
    nocontinue c2' = true ->
    nocontinue c1' = true \/ c2 = AClight.Sskip ->
    path_split (Sloop (LIDouble inv inv) (c1;;c2) AClight.Sskip) res ->
    path_split (Sloop (LISingle inv) c1 c2) res
     *)
| Split_loop_single: forall inv c1 c2 res1 res2 
  (Econt_atom: S_atom_continue res2 = [])
  (Econt_post: S_post_continue res2 = [])
  (Ebasic_pre: all_basic (S_pre res2) = true),
    path_split c1 res1 ->
    path_split c2 res2 ->
    path_split (Sloop (LISingle inv) c1 c2) {|
      S_pre := [(Basic_partial inv,nil)];
      S_path := 
        posts_conn_pres [(Basic_partial inv, nil)] (S_pre res1) ++
        posts_conn_pres [(Basic_partial inv, nil)]
          (atoms_conn_pres (S_atom_normal res1) (S_pre res2)) ++
        posts_conn_pres [(Basic_partial inv, nil)]
          (atoms_conn_pres (S_atom_normal res1)
            (atoms_conn_pres (S_atom_normal res2)
              [(Basic_partial inv, nil)])) ++
        posts_conn_pres [(Basic_partial inv, nil)]
          (atoms_conn_pres (S_atom_continue res1)
              (atoms_conn_pres (S_atom_normal res2)
                [(Basic_partial inv, nil)])) ++
        posts_conn_pres [(Basic_partial inv, nil)]
          (atoms_conn_pres (S_atom_continue res1) (S_pre res2)) ++
        S_path res1 ++ S_path res2 ++
        posts_conn_pres (S_post_normal res1) (S_pre res2) ++
        posts_conn_pres (S_post_normal res1)
            (atoms_conn_pres (S_atom_normal res2) 
              [(Basic_partial inv, [])]) ++
        posts_conn_pres (S_post_continue res1) (S_pre res2) ++
        posts_conn_pres (S_post_continue res1)
            (atoms_conn_pres (S_atom_normal res2) 
              [(Basic_partial inv, [])]) ++
          posts_conn_pres (S_post_normal res2) [(Basic_partial inv, nil)];
      S_post_normal :=
        S_post_break res1 ++ S_post_break res2 ++
        posts_conn_atoms [(Basic_partial inv, nil)] (S_atom_break  res1) ++
        posts_conn_atoms [(Basic_partial inv, nil)]
          (atoms_conn_atoms (S_atom_normal res1) (S_atom_break  res2)) ++
        posts_conn_atoms [(Basic_partial inv, nil)]
          (atoms_conn_atoms (S_atom_continue res1) (S_atom_break  res2)) ++
        posts_conn_atoms (S_post_normal res1) (S_atom_break  res2) ++
        posts_conn_atoms (S_post_continue res1) (S_atom_break  res2);
      S_post_continue := nil;
      S_post_break := nil;
      S_post_return :=
        (S_post_return res1) ++ (S_post_return res2) ++
        posts_conn_returns [(Basic_partial inv, nil)] (S_atom_return res1) ++
        posts_conn_returns [(Basic_partial inv, nil)]
          (atoms_conn_returns (S_atom_normal res1) (S_atom_return res2)) ++
        posts_conn_returns [(Basic_partial inv, nil)]
          (atoms_conn_returns (S_atom_continue res1) (S_atom_return res2)) ++
        posts_conn_returns (S_post_normal res1) (S_atom_return res2) ++
        posts_conn_returns (S_post_continue res1) (S_atom_return res2) ;
      S_atom_normal := nil;
      S_atom_break  := nil;
      S_atom_continue := nil;
      S_atom_return := nil
          (* no continue condition in c2 *)
    |}

 | Split_loop_null: forall stm1 stm2 res1 res2
  (Econt_atom: S_atom_continue res2 = [])
  (Econt_post: S_post_continue res2 = [])
  (Ebasic_pre1: all_basic (S_pre res1) = true)
  (Ebasic_pre2: all_basic (S_pre res2) = true)
  (Ebasic_post1:all_basic (S_post_normal res1) = true)
  (Ebasic_post2:all_basic (S_post_normal res2) = true)
  (Ebasic_post3:all_basic (S_post_continue res1) = true)
  ,
  ((S_atom_normal res1 = []/\S_atom_continue res1 = []) \/ S_atom_normal res2 = [])->
  (S_pre res1 <> []) -> (S_pre res2 <> [])->
    path_split stm1 res1 ->
    path_split stm2 res2 ->
    path_split (Sloop (LINull) stm1 stm2)
      ({|
        S_pre := S_pre res1 ++ atoms_conn_pres (S_atom_normal res1) (S_pre res2) ++ atoms_conn_pres (S_atom_continue res1) (S_pre res2) 
        ;
        S_path := (* path1 ++ path2 ++ nc_post1 * pre2 ++ nc_post1 *n_atom2 * pre1 ++ n_post2 * pre1 ++ n_post2 * nc_atom1 * pre2 *) 
                S_path res1 ++ S_path res2 ++ posts_conn_pres (S_post_normal res1) (S_pre res2) ++ posts_conn_pres (S_post_continue res1) (S_pre res2)
                ++ posts_conn_pres (S_post_normal res2) (S_pre res1) 
                ++ (posts_conn_pres (posts_conn_atoms (S_post_normal res1) (S_atom_normal res2)) (S_pre res1))
                ++ (posts_conn_pres (posts_conn_atoms (S_post_continue res1) (S_atom_normal res2)) (S_pre res1))
                ++ (posts_conn_pres (posts_conn_atoms (S_post_normal res2) (S_atom_normal res1)) (S_pre res2))
                ++ (posts_conn_pres (posts_conn_atoms (S_post_normal res2) (S_atom_continue res1)) (S_pre res2))
                ;
        S_post_normal := (S_post_break res1) ++ (S_post_break res2) 
                        ++ (posts_conn_atoms (S_post_normal res1) (S_atom_break  res2)) 
                        ++ (posts_conn_atoms (S_post_normal res2) (S_atom_break  res1))
                        ++ (posts_conn_atoms (S_post_continue res1) (S_atom_break  res2)) 
                        ++ (posts_conn_atoms (S_post_normal res2) (atoms_conn_atoms (S_atom_normal res1) (S_atom_break  res2)))
                        ++ (posts_conn_atoms (S_post_normal res2) (atoms_conn_atoms (S_atom_continue res1) (S_atom_break  res2)))
                        ++ (posts_conn_atoms (S_post_normal res1) (atoms_conn_atoms (S_atom_normal res2) (S_atom_break  res1)))
                        ++ (posts_conn_atoms (S_post_continue res1) (atoms_conn_atoms (S_atom_normal res2) (S_atom_break  res1)))
                        ;
        S_post_continue := nil;
        S_post_break := nil;
        S_post_return := (S_post_return res1) ++ (S_post_return res2)
                        ++ posts_conn_returns(S_post_normal res1)(S_atom_return res2) 
                        ++ posts_conn_returns(S_post_continue res1)(S_atom_return res2)
                        ++ posts_conn_returns(S_post_normal res2)(S_atom_return res1)
                        ++ (posts_conn_returns (S_post_normal res2) (atoms_conn_returns (S_atom_normal res1) (S_atom_return res2)))
                        ++ (posts_conn_returns (S_post_normal res2) (atoms_conn_returns (S_atom_continue res1) (S_atom_return res2)))
                        ++ (posts_conn_returns (S_post_normal res1) (atoms_conn_returns (S_atom_normal res2) (S_atom_return res1)))
                        ++ (posts_conn_returns (S_post_continue res1) (atoms_conn_returns (S_atom_normal res2) (S_atom_return res1)))
                        ;
        S_atom_normal := S_atom_break  res1 ++ atoms_conn_atoms (S_atom_normal res1) (S_atom_break  res2) ++ atoms_conn_atoms (S_atom_continue res1) (S_atom_break  res2)
                       ++ atoms_conn_atoms (S_atom_normal res2) (S_atom_break  res1);
        S_atom_continue := nil;
        S_atom_break  := nil;
        S_atom_return := S_atom_return res1 ++ atoms_conn_returns (S_atom_normal res1) (S_atom_return res2) ++ atoms_conn_returns (S_atom_continue res1) (S_atom_return res2)
                       ++ atoms_conn_returns (S_atom_normal res2) (S_atom_return res1) ;
        |}) 
*)