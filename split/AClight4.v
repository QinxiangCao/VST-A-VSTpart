
(** The Clight language: a simplified version of Compcert C where all
  expressions are pure and assignments and function calls are
  statements, not expressions. *)

(** TODO:
*  - add definitions for S_split basic operations & if & loop
*  - see if the operations on results can be abstracted
*)


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

(* Higher Order Auxiliary Definitions and Functions
   on dependent results *)

Inductive list_binded_of {R : Type} {binder: R -> Type} : list R -> Type :=
| list_binded_nil : list_binded_of []
| list_binded_cons (r:R) (r': binder r) (l: list R)
                   (l':list_binded_of l) : list_binded_of (r::l).

Fixpoint Capp {A:Type} {binder: A -> Type} 
  {sl1: list A} (cl1 : @list_binded_of A binder sl1)
  {sl2: list A} (cl2 : @list_binded_of A binder sl2)
  : @list_binded_of A binder (sl1 ++ sl2) :=
match cl1 in list_binded_of sl1'
return list_binded_of (sl1' ++ sl2) with
| list_binded_nil => cl2
| list_binded_cons sx cx sl1' cl1' =>
  list_binded_cons sx cx (app sl1' sl2) (Capp cl1' cl2)
end.

Fixpoint Cmap {A B:Type} {binder_a: A -> Type} {binder_b: B -> Type} 
  (f: A -> B ) (binder_f: forall a, binder_a a -> binder_b (f a)) 
    {sl: list A} (cl : @list_binded_of A binder_a sl)
  : @list_binded_of B binder_b (map f sl) :=
match cl in list_binded_of sl'
return list_binded_of (map f sl') with
| list_binded_nil => list_binded_nil
| list_binded_cons sx cx sl' cl' =>
  list_binded_cons (f sx) (binder_f sx cx)
                   (map f sl') (Cmap f binder_f cl')
end.


Infix "+++" := Capp (right associativity, at level 60).




Definition option_map2 {A B C:Type} (f:A->B->C) 
  (o1 : option A) (o2 : option B) : option C :=
  match o1, o2 with
    | Some a, Some b => @Some C (f a b)
    | _, _ => @None C
  end.

(***********************************)
(** Statements *********************)
(***********************************)

Inductive loop_invariant_label :=
| LILNull
| LILSingle
| LILDouble
.

Inductive S_statement : Type :=
| Ssequence (s1: S_statement) (s2: S_statement)
| Sassert
| Sskip
| Sassign (e1:expr) (e2:expr)
| Scall  (id: option ident) (e: expr) (args: list expr)
| Sset (id: ident) (e: expr)
| Sifthenelse  (e: expr) (s1 s2: S_statement)
| Sloop (inv:loop_invariant_label) (s1 s2: S_statement)
| Sbreak 
| Scontinue 
| Sreturn (e: option expr)
.

(***********************************)
(** Assertion annotated statements *)
(***********************************)
Definition assert := (environ -> mpred).

Inductive loop_invariant : loop_invariant_label -> Type :=
| LINull: loop_invariant LILNull
| LISingle : assert -> loop_invariant LILSingle
| LIDouble : assert -> assert -> loop_invariant LILDouble.


Inductive C_statement : S_statement -> Type :=
| Csequence: forall (s1: S_statement) (s2: S_statement)
      (c1: C_statement s1) (c2: C_statement s2),
    C_statement (Ssequence s1 s2)
| Cassert: forall (a: assert),
    C_statement Sassert
| Cskip: C_statement Sskip
| Cgiven : forall (A:Type) (HA: inhabited A) (c: S_statement)
    (stm': A -> C_statement c),
    C_statement c
| Cexgiven:  forall (A:Type) (HA: inhabited A) 
    (ass: A -> assert)
    (c: S_statement)
    (a_stm': A -> C_statement c),
    C_statement (Ssequence Sassert (Ssequence Sassert c ))
(* EX a. ass *)
(* Given a
   { ass }
    c ...

*)

    (* C_statement c *)
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
| Cloop : forall (invl: loop_invariant_label) 
      (inv: loop_invariant invl) (s1 s2: S_statement)
      (c1: C_statement s1) (c2: C_statement s2),
    C_statement (Sloop invl s1 s2)
| Cbreak : C_statement (Sbreak)
| Ccontinue : C_statement (Scontinue)
| Creturn : forall (e: option expr), C_statement (Sreturn e)
.


(***********************************)
(** Simple Split Results  *)
(***********************************)

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



(***********************************)
(** Dependent split results   *)
(***********************************)


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

(***********************************)
(** Simple operations on results *)
(***********************************)

Definition atom_conn_return atom1 atom2 :=
  match atom1, atom2 with
  | mk_atom path1, mk_atom_ret path2 retval =>
      mk_atom_ret (path1 ++ path2) retval
  end.

Definition atom_conn_returns atom1 atoms2 :=
  map (atom_conn_return atom1) atoms2.

Definition atoms_conn_returns atoms1 atoms2 :=
  concat (map (fun atom1 => atom_conn_returns atom1 atoms2) atoms1).

Definition atom_conn_atom atom1 atom2 :=
  match atom1, atom2 with
  | mk_atom path1, mk_atom path2 =>
      mk_atom (path1 ++ path2)
  end.

Definition atom_conn_atoms atom1 atoms2 :=
  map (atom_conn_atom atom1) atoms2.

Definition atoms_conn_atoms atoms1 atoms2 :=
  concat (map (fun atom1 => atom_conn_atoms atom1 atoms2) atoms1).

Definition atom_conn_Spre atom1 s_pre2 :=
  match atom1, s_pre2 with
  | mk_atom path1, mk_S_partial_pre path2 =>
      mk_S_partial_pre (path1 ++ path2)
  end.


Definition atom_conn_Spres atom1 s_pres2 :=
    map (atom_conn_Spre atom1) s_pres2.


Fixpoint atoms_conn_Spres atoms1 s_pres2 :=
  match atoms1 with
  | [] => []
  | atom1 :: atoms1' =>
    atom_conn_Spres atom1 s_pres2 ++ atoms_conn_Spres atoms1' s_pres2
  end.

Definition Spost_conn_atom s_post1 atom2 :=
  match s_post1 with
  | mk_S_partial_post path1 =>
    match atom2 with
    | mk_atom path2 =>
        mk_S_partial_post (path1 ++ path2)
    end
  end.

Definition Sposts_conn_atom s_posts1 atom2 :=
  map (fun s_post1 => Spost_conn_atom s_post1 atom2) s_posts1.


Definition Spost_conn_return s_post1 atom2 :=
  match s_post1 with
  | mk_S_partial_post path1 =>
    match atom2 with
    | mk_atom_ret path2 retval =>
        mk_S_partial_post_ret (path1 ++ path2) retval
    end
  end.

  
Definition Sposts_conn_return s_posts1 atom2 :=
  map (fun s_post1 => Spost_conn_return s_post1 atom2) s_posts1.


Fixpoint Sposts_conn_atoms s_posts1 atoms2 :=
  match atoms2 with
  | [] => []
  | atom2 :: atoms2' =>
    Sposts_conn_atom s_posts1 atom2 ++ Sposts_conn_atoms s_posts1 atoms2'
  end.


Fixpoint Sposts_conn_returns s_posts1 atoms2 :=
  match atoms2 with
  | [] => []
  | atom2 :: atoms2' =>
    Sposts_conn_return s_posts1 atom2 ++ Sposts_conn_returns s_posts1 atoms2'
  end.


Definition Spost_conn_Spre
  (s_post1: S_partial_post)
  (s_pre2: S_partial_pre) : S_full_path :=
match s_post1 with
| mk_S_partial_post path1 =>
  match s_pre2 with
  | mk_S_partial_pre path2 =>
      mk_S_full_path (path1 ++ path2)
  end
end.

Definition Spost_conn_Spres 
  (s_post1: S_partial_post)
  (s_pres2: S_partial_pres) : S_full_paths :=
map (fun s_pre2 => Spost_conn_Spre s_post1 s_pre2) s_pres2.

Fixpoint Sposts_conn_Spres 
  (s_posts1: S_partial_posts)
  (s_pres2: S_partial_pres) : S_full_paths :=
  match s_posts1 with
  | [] => []
  | s_post1 :: s_posts1' =>
    Spost_conn_Spres s_post1 s_pres2 ++ 
    Sposts_conn_Spres s_posts1' s_pres2
  end.


(***********************************)
(** Dependent Operations on split results *)
(***********************************)

Fixpoint atom_conn_Cpre s_atom1 { s_pre2 } (c_pre2: C_partial_pre s_pre2) : C_partial_pre (atom_conn_Spre s_atom1 s_pre2) :=
match s_atom1 with
  | mk_atom path1 =>
  match c_pre2 in C_partial_pre s_pre2'
  return C_partial_pre (atom_conn_Spre (mk_atom path1) s_pre2') with
  | mk_C_partial_pre path2 post2 =>
      mk_C_partial_pre (path1 ++ path2) post2
  | bind_C_partial_pre A HA s_pre2 c_pre2' =>
      bind_C_partial_pre A HA (atom_conn_Spre (mk_atom path1) s_pre2)
        (fun a => atom_conn_Cpre (mk_atom path1) (c_pre2' a))
  end
end.


Definition atom_conn_Cpres s_atom1 { s_pres2 } (c_pres2: C_partial_pres s_pres2) : C_partial_pres (atom_conn_Spres s_atom1 s_pres2) :=
  Cmap (atom_conn_Spre s_atom1) (@atom_conn_Cpre s_atom1) c_pres2.

Fixpoint atoms_conn_Cpres 
  (atoms: atoms)
  {Spres: S_partial_pres}
  (Cpres: C_partial_pres Spres) 
  : (C_partial_pres (atoms_conn_Spres atoms Spres)) :=
  match atoms with
  | nil => list_binded_nil
  | atom :: atoms' =>
      Capp (atom_conn_Cpres atom Cpres)
            (atoms_conn_Cpres atoms' Cpres)
  end.


Fixpoint Cpost_conn_atom { s_post1 } 
  (c_post1 : C_partial_post s_post1) atom2
  : C_partial_post (Spost_conn_atom s_post1 atom2) :=
  match atom2 with
  | mk_atom path2 =>
  match c_post1 in C_partial_post s_post1'
  return C_partial_post (Spost_conn_atom s_post1' (mk_atom path2)) with
  | mk_C_partial_post pre1 path1 =>
      mk_C_partial_post pre1 (path1 ++ path2)
  | bind_C_partial_post A HA s_post1 c_post1' =>
      bind_C_partial_post A HA (Spost_conn_atom s_post1 (mk_atom path2))
        (fun a => Cpost_conn_atom (c_post1' a) (mk_atom path2))
  end
end.


Fixpoint Cposts_conn_atom {s_posts1} (c_posts1 : C_partial_posts s_posts1) atom2 : C_partial_posts (Sposts_conn_atom s_posts1 atom2) :=
  Cmap(fun s_post1 => Spost_conn_atom s_post1 atom2)
       (fun s_post1 c_post1 => 
            @Cpost_conn_atom s_post1 c_post1 atom2)
  c_posts1.


Fixpoint Cposts_conn_atoms 
  {s_posts1 : S_partial_posts}
  (c_posts1 : C_partial_posts s_posts1) 
  (atoms2: atoms)
  : (C_partial_posts (Sposts_conn_atoms s_posts1 atoms2)):=
  match atoms2 with
  | nil => list_binded_nil
  | atom :: atoms' =>
      Capp (Cposts_conn_atom c_posts1 atom )
            (Cposts_conn_atoms c_posts1 atoms')
  end.



Fixpoint Cpost_conn_return { s_post1 } 
  (c_post1 : C_partial_post s_post1) atom2
  : C_partial_post_ret (Spost_conn_return s_post1 atom2) :=
  match atom2 with
  | mk_atom_ret path2 retval =>
  match c_post1 in C_partial_post s_post1'
  return C_partial_post_ret (Spost_conn_return s_post1' (mk_atom_ret path2 retval)) with
  | mk_C_partial_post pre1 path1 =>
      mk_C_partial_post_ret pre1 (path1 ++ path2) retval
  | bind_C_partial_post A HA s_post1 c_post1' =>
      bind_C_partial_post_ret A HA (Spost_conn_return s_post1 (mk_atom_ret path2 retval))
        (fun a => Cpost_conn_return (c_post1' a) (mk_atom_ret path2 retval))
  end
end.


Fixpoint Cposts_conn_return {s_posts1} (c_posts1 : C_partial_posts s_posts1) atom2 : C_partial_post_rets (Sposts_conn_return s_posts1 atom2) :=
  Cmap(fun s_post1 => Spost_conn_return s_post1 atom2)
        (fun s_post1 c_post1 => 
            @Cpost_conn_return s_post1 c_post1 atom2)
  c_posts1.


Fixpoint Cposts_conn_returns 
  {s_posts1 : S_partial_posts}
  (c_posts1 : C_partial_posts s_posts1) 
  (atoms2: atom_rets)
  : (C_partial_post_rets (Sposts_conn_returns s_posts1 atoms2)):=
  match atoms2 with
  | nil => list_binded_nil
  | atom :: atoms' =>
      Capp (Cposts_conn_return c_posts1 atom )
            (Cposts_conn_returns c_posts1 atoms')
  end.


Fixpoint Cpost_conn_Cpre_aux
  (pre: assert)
  (path1: path)
  {s_pre2: S_partial_pre}
  (c_pre2: C_partial_pre s_pre2) : 
  C_full_path (Spost_conn_Spre (mk_S_partial_post path1) s_pre2) :=
match c_pre2 in C_partial_pre s_pre2'
return C_full_path (Spost_conn_Spre (mk_S_partial_post path1) s_pre2') with
| mk_C_partial_pre path2 post =>
    mk_C_full_path pre (path1 ++ path2) post
| bind_C_partial_pre A HA s_pre2 c_pre2' =>
    bind_C_full_path A HA 
      (Spost_conn_Spre (mk_S_partial_post path1) s_pre2)
      (fun a => Cpost_conn_Cpre_aux pre path1 (c_pre2' a))
end.

Fixpoint Cpost_conn_Cpre
  {s_post1: S_partial_post}
  (c_post1: C_partial_post s_post1)
  {s_pre2: S_partial_pre}
  (c_pre2: C_partial_pre s_pre2) :
  C_full_path (Spost_conn_Spre s_post1 s_pre2) :=
match c_post1 in C_partial_post s_post1'
return C_full_path (Spost_conn_Spre s_post1' s_pre2) with
| mk_C_partial_post pre path1 =>
    Cpost_conn_Cpre_aux pre path1 c_pre2
| bind_C_partial_post A HA s_post1 c_post1' =>
    bind_C_full_path A HA 
      (Spost_conn_Spre s_post1 s_pre2)
      (fun a => Cpost_conn_Cpre (c_post1' a) c_pre2)
end.




Definition Cpost_conn_Cpres 
  {s_post1: S_partial_post}
  (c_post1: C_partial_post s_post1)
  {s_pres2: S_partial_pres}
  (c_pres2: C_partial_pres s_pres2 ) 
  : C_full_paths (Spost_conn_Spres s_post1 s_pres2) :=
Cmap 
  (fun s_pre2 => Spost_conn_Spre s_post1 s_pre2)
  (fun s_pre2 c_pre2 => 
       @Cpost_conn_Cpre s_post1 c_post1 s_pre2 c_pre2)
  c_pres2.



Fixpoint Cposts_conn_Cpres
  {s_posts1 : S_partial_posts}
  (c_posts1 : C_partial_posts s_posts1)
  {s_pres2: S_partial_pres}
  (c_pres2: C_partial_pres s_pres2)
  : (C_full_paths (Sposts_conn_Spres s_posts1 s_pres2)):=
  match c_posts1 in list_binded_of s_posts1'
  return C_full_paths (Sposts_conn_Spres s_posts1' s_pres2) with
  | list_binded_nil => list_binded_nil
  | list_binded_cons s_post1 c_post1 s_posts' c_posts' =>
      Capp (Cpost_conn_Cpres c_post1 c_pres2)
           (Cposts_conn_Cpres c_posts' c_pres2)
  end.



(***********************************)
(** Simple result makers *)
(***********************************)

Definition S_split_sequence res1 res2 := 
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


Definition S_split_ifthenelse (e: expr) res1 res2 := 
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


Definition S_split_loop0 res1 res2 := 
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

Definition S_split_loop1 res1 res2 := 
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

Definition S_split_loop2 res1 res2 := 
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

Definition S_split_loop inv res1 res2 := 
  match inv with
  | LILNull => S_split_loop0 res1 res2
  | LILSingle => S_split_loop1 res1 res2
  | LILDouble => S_split_loop2 res1 res2
  end.

Definition S_split_assert := 
  mk_S_result 
  (* S_pre *)           [ mk_S_partial_pre nil ]
  (* S_path *)          []
  (* S_post_normal *)   [ mk_S_partial_post nil ]
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   []
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
.


Definition S_split_skip := 
  mk_S_result 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   []
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
.


Definition S_split_assign (e1 e2: expr) := 
  mk_S_result 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   []
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
.


Definition S_split_call 
  (id: option ident) (e: expr) (args: list expr) := 
  mk_S_result 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   []
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
.


Definition S_split_set (id: ident) (e: expr) := 
  mk_S_result 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   []
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
.


Definition S_split_break := 
  mk_S_result 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   []
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
.

Definition S_split_continue := 
  mk_S_result 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   []
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
.

Definition S_split_return (e: option expr) := 
  mk_S_result 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   []
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
.


Fixpoint S_split (s: S_statement) : S_result :=
  match s with
  | Ssequence s1 s2 =>
      let res1 := S_split s1 in
      let res2 := S_split s2 in
      S_split_sequence res1 res2
  | Sassert => 
      S_split_assert
  | Sskip => 
      S_split_skip
  | Sassign e1 e2 =>
      S_split_assign e1 e2
  | Scall id e args =>
      S_split_call id e args
  | Sset id e =>
      S_split_set id e
  | Sbreak =>
      S_split_break
  | Scontinue =>
      S_split_continue
  | Sreturn e =>
      S_split_return e
  | Sifthenelse e s1 s2 => 
      let res1 := S_split s1 in
      let res2 := S_split s2 in
      S_split_ifthenelse e res1 res2
  | Sloop inv s1 s2 => 
      let res1 := S_split s1 in
      let res2 := S_split s2 in
      S_split_loop inv res1 res2
  end.



(***********************************)
(** dependent projectors of A -> X *)
(***********************************)

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


Definition C_result_proj_C_post_break (A : Type) (c_res: A -> C_result s_res) : A -> C_partial_posts (s_post_break) :=
  fun a =>
    match (c_res a) 
    with
    | mk_C_result _ _ _ _ _ _ _ c_post_break _ _ _ _ _ _ _ _ =>
      c_post_break
    end.

Definition C_result_proj_C_post_continue (A : Type) (c_res: A -> C_result s_res) : A -> C_partial_posts (s_post_continue):=
fun a =>
match (c_res a) 
with
| mk_C_result _ _ _ _ _ _ _ _ _ c_post_continue _ _ _ _ _ _ =>
c_post_continue
end.

Definition C_result_proj_C_post_return (A : Type) (c_res: A -> C_result s_res) : A -> C_partial_post_rets (s_post_return) :=
fun a =>
match (c_res a)
with
| mk_C_result _ _ _ _ _ _ _ _ _ _ _ C_post_return _ _ _ _ =>
C_post_return
end.

Definition C_result_proj_C_path (A : Type) (c_res: A -> C_result s_res) : A -> C_full_paths (s_path) :=
fun a =>
match (c_res a)
with
| mk_C_result _ _ _ C_path  _ _ _ _ _ _ _ _ _ _ _ _ =>
C_path
end.

End Cres_proj.




(***********************************)
(** dependent result makers *)
(***********************************)


Notation "{ }" := list_binded_nil (format "{ }").

(* Notation "[[ ]]" := list_binded_nil (format "[[ ]]"). *)
(* Notation "[[ x ]]" := (list_binded_cons _ x _ list_binded_nil). *)
Notation "{ x }" := (list_binded_cons _ x _ list_binded_nil).
(* Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope. *)
(* Infix "::" := cons (at level 60, right associativity) : list_scope. *)


Definition C_split_assert (a: assert) : C_result (S_split Sassert) :=
  mk_C_result
  (* S_pre *)           [ mk_S_partial_pre nil ]
  (* C_pre *)           { (mk_C_partial_pre nil a) }
  (* S_path *)          []
  (* C_path *)          {}
  (* S_post_normal *)   [ mk_S_partial_post nil]
  (* C_post_normal *)   { mk_C_partial_post a nil }
  (* S_post_break *)    []
  (* C_post_break *)    {}
  (* S_post_continue *) []
  (* C_post_continue *) {}
  (* S_post_return *)   []
  (* C_post_return *)   {}
  (* S_atom_normal *)   []
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
.

Definition C_split_sequence 
(s1 s2 : S_statement)
(* (c1: C_statement s1) (c2: C_statement s2) *)
: C_result (S_split s1) ->
  C_result (S_split s2) ->
  C_result (S_split (Ssequence s1 s2)) :=
fun c_res1 c_res2 =>
match 
  c_res1 in C_result s_res1,
  c_res2 in C_result s_res2
  return (C_result (S_split_sequence s_res1 s_res2))
with
  | no_C_result, _ 
  | _, no_C_result => no_C_result
  | mk_C_result s_pre1 c_pre1 s_path1 c_path1 
      s_post_normal1 c_post_normal1 
      s_post_break1 c_post_break1 
      s_post_continue1 c_post_continue1 
      s_post_return1 c_post_return1
      s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1,
    mk_C_result s_pre2 c_pre2 s_path2 c_path2 
      s_post_normal2 c_post_normal2 
      s_post_break2 c_post_break2 
      s_post_continue2 c_post_continue2 
      s_post_return2 c_post_return2
      s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2 =>
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
.




(* EX a. 
   Given a...

   { Q(a) }

   Bind a. 
    {EX a . P(a)}
    ...
    {Q(a)}

*)

Definition C_split_given (s_res : S_result) (A : Type) (HA: inhabited A) :
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

Definition C_split_exgiven (s_res: S_result) (A: Type) (HA: inhabited A) (c_ass': A -> assert) : (A -> C_result s_res) ->
C_result (S_split_sequence S_split_assert s_res ) :=
match s_res with
| mk_S_result s_pre s_path s_post_normal s_post_break s_post_continue s_post_return s_atom_normal s_atom_break s_atom_continue s_atom_return =>
fun c_res' =>
let ex_ass := exp c_ass' in
let c_pre := C_result_proj_C_pre A c_res' in
let c_pre := flatten_partial_pres_binds HA (s_pre) c_pre in
let c_post_normal := C_result_proj_C_post_normal A c_res' in
let c_post_normal := flatten_partial_posts_binds HA (s_post_normal) c_post_normal in
let c_post_break := C_result_proj_C_post_break A c_res' in
let c_post_break := flatten_partial_posts_binds HA (s_post_break) c_post_break in
let c_post_continue := C_result_proj_C_post_continue A c_res' in
let c_post_continue := flatten_partial_posts_binds HA (s_post_continue) c_post_continue in
let c_post_return := C_result_proj_C_post_return A c_res' in
let c_post_return := flatten_partial_post_rets_binds HA (s_post_return) c_post_return in
let c_path := C_result_proj_C_path A c_res' in
let c_path := flatten_full_paths_binds HA (s_path) c_path in

let ass_post_normal_C := bind_C_partial_post A HA 
          (mk_S_partial_post nil)
          (fun a => mk_C_partial_post (c_ass' a) nil) in
let ass_post_normal_S := mk_S_partial_post nil in

mk_C_result
(* S_pre *)
  ( [ mk_S_partial_pre nil ] ++ atoms_conn_Spres [] s_pre)
(* C_pre *)
  ( Capp ({ (mk_C_partial_pre nil ex_ass) }) (atoms_conn_Cpres [] c_pre))
(* S_path *)
  (s_path ++ 
    Sposts_conn_Spres [ass_post_normal_S] s_pre)
(* C_path *)
  (c_path +++ 
    Cposts_conn_Cpres { ass_post_normal_C } c_pre)
(* S_post_normal *)
  (s_post_normal ++ 
    Sposts_conn_atoms [ass_post_normal_S] s_atom_normal)
(* C_post_normal *)
  (c_post_normal +++ 
    Cposts_conn_atoms { ass_post_normal_C } s_atom_normal)
(* S_post_break *)
  (s_post_break ++ 
    Sposts_conn_atoms [ass_post_normal_S] s_atom_break)
(* C_post_break *)
  (c_post_break +++
    Cposts_conn_atoms { ass_post_normal_C } s_atom_break)
(* S_post_continue *)
  (s_post_continue ++ 
    Sposts_conn_atoms [ass_post_normal_S] s_atom_continue)
(* C_post_continue *)
  ( c_post_continue +++ 
    Cposts_conn_atoms { ass_post_normal_C } s_atom_continue)
(* S_post_return *)
  ( s_post_return ++ 
    Sposts_conn_returns [ass_post_normal_S] s_atom_return)
(* C_post_return *)
  ( c_post_return +++ 
    Cposts_conn_returns { ass_post_normal_C } s_atom_return)
(* S_atom_normal *)
  (atoms_conn_atoms [] s_atom_normal)
(* S_atom_break *)
  ( atoms_conn_atoms [] s_atom_break)
(* S_atom_continue *)
  ( atoms_conn_atoms [] s_atom_continue)
(* S_atom_return *)
  ( atoms_conn_returns [] s_atom_return)

| no_S_result => fun _ => no_C_result
end.


let ex_split := C_split_assert ex_ass in
let c_split := C_split_given (S_split (Ssequence Sassert s)) A HA
    (fun a:A => C_split_sequence Sassert s  
                  (C_split_assert (c_ass' a)) (c_res' a)) in
C_split_sequence Sassert (Ssequence Sassert s) ex_split c_split.

Definition C_split_skip : C_result (S_split Sskip).
Admitted.

Definition C_split_assign e1 e2 : C_result (S_split (Sassign e1 e2)).
Admitted.

Definition C_split_call id e args : C_result (S_split (Scall id e args)).
Admitted.

Definition C_split_set e1 e2 : C_result (S_split (Sset e1 e2)).
Admitted.

Definition C_split_break : C_result (S_split Sbreak).
Admitted.

Definition C_split_continue : C_result (S_split Scontinue).
Admitted.

Definition C_split_return e : C_result (S_split (Sreturn e)).
Admitted.




Definition C_split_ifthenelse (e: expr)
(s1 s2 : S_statement)
: C_result (S_split s1) ->
  C_result (S_split s2) ->
  C_result (S_split (Sifthenelse e s1 s2)).
Admitted.

Definition C_split_loop0
(s1 s2 : S_statement)
: C_result (S_split s1) ->
  C_result (S_split s2) ->
  C_result (S_split (Sloop LILNull s1 s2)).
Admitted.

Definition C_split_loop1 (inv: assert)
(s1 s2 : S_statement)
: C_result (S_split s1) ->
  C_result (S_split s2) ->
  C_result (S_split (Sloop LILSingle s1 s2)).
Admitted.


Definition C_split_loop2 (inv1: assert) (inv2: assert)
(s1 s2 : S_statement)
: C_result (S_split s1) ->
  C_result (S_split s2) ->
  C_result (S_split (Sloop LILDouble s1 s2)).
Admitted.

Definition C_split_loop {invl} (inv: loop_invariant invl)
(s1 s2 : S_statement)
(c_res1 : C_result (S_split s1))
(c_res2 : C_result (S_split s2)) :
  C_result (S_split (Sloop invl s1 s2)) :=
match inv in loop_invariant invl' 
return C_result (S_split (Sloop invl' s1 s2)) with
| LINull => 
    C_split_loop0 s1 s2 c_res1 c_res2
| LISingle inv =>
    C_split_loop1 inv s1 s2 c_res1 c_res2
| LIDouble inv1 inv2 =>
    C_split_loop2 inv1 inv2 s1 s2 c_res1 c_res2
end.

Fixpoint C_split (s: S_statement) (c: C_statement s) : C_result (S_split s) :=
match c as c0 in C_statement s0
  return C_result (S_split s0)
with
| Csequence s1 s2 c1 c2 =>
    C_split_sequence s1 s2 (C_split s1 c1) (C_split s2 c2)
| Cassert a =>
    C_split_assert a
| Cskip => 
    C_split_skip
| Cgiven A HA c a_stm' =>
    C_split_given (S_split c) A HA (fun a =>  C_split c (a_stm' a))
| Cexgiven A HA ass c a_stm' =>
    C_split_exgiven c A HA ass
      (fun a =>  C_split c (a_stm' a))
| Cassign e1 e2 =>
    C_split_assign e1 e2
| Ccall id e args =>
    C_split_call id e args
| Cset id e =>
    C_split_set id e
| Cifthenelse e s1 s2 c1 c2 =>
    C_split_ifthenelse e s1 s2 (C_split s1 c1) (C_split s2 c2)
| Cloop invl inv s1 s2 c1 c2 =>
    C_split_loop inv s1 s2 (C_split s1 c1) (C_split s2 c2)
| Cbreak =>
    C_split_break
| Ccontinue =>
    C_split_continue
| Creturn e =>
    C_split_return e
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