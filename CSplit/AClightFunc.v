
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
Require Import VST.veric.mpred.
Require Import VST.msl.seplog.
Require Import VST.veric.SeparationLogic.
Require Import VST.veric.juicy_extspec.
Require Import Csplit.AClight.
Import ListNotations.


Definition Sapp :=
  fun {A : Type} =>
  fix Sapp (l m : list A) {struct l} : list A :=
    match l with
    | nil => m
    | a :: l1 => a :: Sapp l1 m
    end.


Local Close Scope list_scope.

Infix "::" := cons (at level 60, right associativity) : aclight_scope.
Notation "[ ]" := nil (format "[ ]") : aclight_scope.
Notation "[ x ]" := (cons x nil) : aclight_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : aclight_scope.
Infix "+/+" := Sapp (right associativity, at level 60) : aclight_scope.

Open Scope aclight_scope.

Delimit Scope aclight_scope with aclight.

Bind Scope aclight_scope with list.


Definition Sconcat :=
  fun {A : Type} =>
  fix Sconcat (l : list (list A)) : list A :=
    match l with
    | nil => nil
    | x :: l0 => x +/+ Sconcat l0
    end.


Definition Smap :=
  fun {A B : Type} (f : A -> B) =>
  fix Smap (l : list A) : list B :=
  match l with
  | nil => nil
  | a :: t => f a :: Smap t
  end.



Fixpoint Cmap {A B:Type} {binder_a: A -> Type} {binder_b: B -> Type} 
  (f: A -> B ) (binder_f: forall a, binder_a a -> binder_b (f a)) 
    {sl: list A} (cl : @list_binded_of A binder_a sl)
  : @list_binded_of B binder_b (Smap f sl) :=
match cl in list_binded_of sl'
return list_binded_of (Smap f sl') with
| list_binded_nil => list_binded_nil
| list_binded_cons sx cx sl' cl' =>
  list_binded_cons (f sx) (binder_f sx cx)
                   (Smap f sl') (Cmap f binder_f cl')
end.




Definition option_map2 {A B C:Type} (f:A->B->C) 
  (o1 : option A) (o2 : option B) : option C :=
  match o1, o2 with
    | Some a, Some b => @Some C (f a b)
    | _, _ => @None C
  end.


Definition path:= list (bool * expr + atom_statement) .

(***********************************)
(** Simple operations on results *)
(***********************************)

Definition atom_conn_return atom1 atom2 :=
  match atom1, atom2 with
  | mk_atom path1, mk_atom_ret path2 retval =>
      mk_atom_ret (path1 +/+ path2) retval
  end.


Definition atom_conn_returns atom1 atoms2 :=
  Smap (atom_conn_return atom1) atoms2.

Definition atoms_conn_returns atoms1 atoms2 :=
  Sconcat (Smap (fun atom1 => atom_conn_returns atom1 atoms2) atoms1).

Definition atom_conn_atom atom1 atom2 :=
  match atom1, atom2 with
  | mk_atom path1, mk_atom path2 =>
      mk_atom (path1 +/+ path2)
  end.

Definition atom_conn_atoms atom1 atoms2 :=
  Smap (atom_conn_atom atom1) atoms2.

Definition atoms_conn_atoms atoms1 atoms2 :=
  Sconcat (Smap (fun atom1 => atom_conn_atoms atom1 atoms2) atoms1).

Definition atom_conn_Spre atom1 s_pre2 :=
  match atom1, s_pre2 with
  | mk_atom path1, mk_S_partial_pre path2 =>
      mk_S_partial_pre (path1 +/+ path2)
  end.


Definition atom_conn_Spres atom1 s_pres2 :=
    Smap (atom_conn_Spre atom1) s_pres2.


Fixpoint atoms_conn_Spres atoms1 s_pres2 :=
  match atoms1 with
  | [] => []
  | atom1 :: atoms1' =>
    atom_conn_Spres atom1 s_pres2 +/+ atoms_conn_Spres atoms1' s_pres2
  end.

Definition Spost_conn_atom s_post1 atom2 :=
  match s_post1 with
  | mk_S_partial_post path1 =>
    match atom2 with
    | mk_atom path2 =>
        mk_S_partial_post (path1 +/+ path2)
    end
  end.

Definition Sposts_conn_atom s_posts1 atom2 :=
  Smap (fun s_post1 => Spost_conn_atom s_post1 atom2) s_posts1.


Definition Spost_conn_return s_post1 atom2 :=
  match s_post1 with
  | mk_S_partial_post path1 =>
    match atom2 with
    | mk_atom_ret path2 retval =>
        mk_S_partial_post_ret (path1 +/+ path2) retval
    end
  end.

  
Definition Sposts_conn_return s_posts1 atom2 :=
  Smap (fun s_post1 => Spost_conn_return s_post1 atom2) s_posts1.


Fixpoint Sposts_conn_atoms s_posts1 atoms2 :=
  match atoms2 with
  | [] => []
  | atom2 :: atoms2' =>
    Sposts_conn_atom s_posts1 atom2 +/+ Sposts_conn_atoms s_posts1 atoms2'
  end.


Fixpoint Sposts_conn_returns s_posts1 atoms2 :=
  match atoms2 with
  | [] => []
  | atom2 :: atoms2' =>
    Sposts_conn_return s_posts1 atom2 +/+ Sposts_conn_returns s_posts1 atoms2'
  end.


Definition Spost_conn_Spre
  (s_post1: S_partial_post)
  (s_pre2: S_partial_pre) : S_full_path :=
match s_post1 with
| mk_S_partial_post path1 =>
  match s_pre2 with
  | mk_S_partial_pre path2 =>
      mk_S_full_path (path1 +/+ path2)
  end
end.

Notation Spost_conn_Spres s_post1 s_pres2 :=
(Smap (fun s_pre2 => Spost_conn_Spre s_post1 s_pre2) s_pres2).

Fixpoint Sposts_conn_Spres 
  (s_posts1: S_partial_posts)
  (s_pres2: S_partial_pres) : S_full_paths :=
  match s_posts1 with
  | [] => []
  | s_post1 :: s_posts1' =>
    Spost_conn_Spres s_post1 s_pres2 +/+ 
    Sposts_conn_Spres s_posts1' s_pres2
  end.

Definition add_exp_to_Spre b e 
( s_pre : S_partial_pre ) :=
match s_pre with
| mk_S_partial_pre path =>
    mk_S_partial_pre ((inl (b, e))::path)
end.

Definition add_exp_to_Spres b e s_pres :=
Smap (add_exp_to_Spre b e) s_pres.

Definition add_exp_to_atom b e (atom: atom) :=
match atom with
| mk_atom path =>
   mk_atom ((inl (b, e))::path)
end.

Definition add_exp_to_atoms b e atoms :=
Smap (add_exp_to_atom b e) atoms.


Definition add_exp_to_ret_atom b e (atom: atom_ret) :=
match atom with
| mk_atom_ret path retval =>
    mk_atom_ret ((inl (b, e))::path) retval
end.

Definition add_exp_to_ret_atoms b e atoms :=
Smap (add_exp_to_ret_atom b e) atoms.

Definition add_P_to_Spre s_pre :=
match s_pre with
| mk_S_partial_pre path =>
    mk_S_full_path path
end.

Notation add_P_to_Spres := (Smap add_P_to_Spre).

Definition add_P_to_atom s_atom :=
match s_atom with
| mk_atom path =>
    mk_S_partial_post path
end.

Notation add_P_to_atoms := (Smap add_P_to_atom).

Definition add_P_to_atom_ret s_atom :=
match s_atom with
| mk_atom_ret path retval =>
    mk_S_partial_post_ret path retval
end.

Notation add_P_to_atom_rets := (Smap add_P_to_atom_ret).

Definition add_Q_to_Spost s_post :=
match s_post with
| mk_S_partial_post path =>
    mk_S_full_path path
end.

Notation add_Q_to_Sposts := (Smap add_Q_to_Spost).

Definition add_Q_to_atom s_atom :=
match s_atom with
| mk_atom path =>
    mk_S_partial_pre path
end.

Fixpoint add_Q_to_atoms s_atoms :=
  match s_atoms with
  | nil => nil
  | s_atom :: s_atoms' =>
    (add_Q_to_atom s_atom) :: add_Q_to_atoms s_atoms'
  end.

(* Notation add_Q_to_atoms := (Smap add_Q_to_atom). *)

(***********************************)
(** Dependent Operations on split results *)
(***********************************)

Definition atom_conn_Cpre s_atom1 { s_pre2 } (c_pre2: C_partial_pre s_pre2) : C_partial_pre (atom_conn_Spre s_atom1 s_pre2) :=
match s_atom1 with
  | mk_atom path1 =>
  match c_pre2 in C_partial_pre s_pre2'
  return C_partial_pre (atom_conn_Spre (mk_atom path1) s_pre2') with
  | mk_C_partial_pre path2 post2 =>
      mk_C_partial_pre (path1 +/+ path2) post2
  (* | bind_C_partial_pre A HA s_pre2 c_pre2' =>
      bind_C_partial_pre A HA (atom_conn_Spre (mk_atom path1) s_pre2)
        (fun a => atom_conn_Cpre (mk_atom path1) (c_pre2' a)) *)
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


Definition Cpost_conn_atom { s_post1 } 
  (c_post1 : C_partial_post s_post1) atom2
  : C_partial_post (Spost_conn_atom s_post1 atom2) :=
  match atom2 with
  | mk_atom path2 =>
  match c_post1 in C_partial_post s_post1'
  return C_partial_post (Spost_conn_atom s_post1' (mk_atom path2)) with
  | mk_C_partial_post pre1 path1 =>
      mk_C_partial_post pre1 (path1 +/+ path2)
  end
end.


Definition Cposts_conn_atom {s_posts1} (c_posts1 : C_partial_posts s_posts1) atom2 : C_partial_posts (Sposts_conn_atom s_posts1 atom2) :=
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



Definition Cpost_conn_return { s_post1 } 
  (c_post1 : C_partial_post s_post1) atom2
  : C_partial_post_ret (Spost_conn_return s_post1 atom2) :=
  match atom2 with
  | mk_atom_ret path2 retval =>
  match c_post1 in C_partial_post s_post1'
  return C_partial_post_ret (Spost_conn_return s_post1' (mk_atom_ret path2 retval)) with
  | mk_C_partial_post pre1 path1 =>
      mk_C_partial_post_ret pre1 (path1 +/+ path2) retval
  end
end.


Definition Cposts_conn_return {s_posts1} (c_posts1 : C_partial_posts s_posts1) atom2 : C_partial_post_rets (Sposts_conn_return s_posts1 atom2) :=
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


Definition Cpost_conn_Cpre_aux
  (pre: assert)
  (path1: path)
  {s_pre2: S_partial_pre}
  (c_pre2: C_partial_pre s_pre2) : 
  C_full_path (Spost_conn_Spre (mk_S_partial_post path1) s_pre2) :=
match c_pre2 in C_partial_pre s_pre2'
return C_full_path (Spost_conn_Spre (mk_S_partial_post path1) s_pre2') with
| mk_C_partial_pre path2 post =>
    mk_C_full_path pre (path1 +/+ path2) post
(* | bind_C_partial_pre A HA s_pre2 c_pre2' =>
    bind_C_full_path A HA 
      (Spost_conn_Spre (mk_S_partial_post path1) s_pre2)
      (fun a => Cpost_conn_Cpre_aux pre path1 (c_pre2' a)) *)
end.

Definition Cpost_conn_Cpre
  {s_post1: S_partial_post}
  (c_post1: C_partial_post s_post1)
  {s_pre2: S_partial_pre}
  (c_pre2: C_partial_pre s_pre2) :
  C_full_path (Spost_conn_Spre s_post1 s_pre2) :=
match c_post1 in C_partial_post s_post1'
return C_full_path (Spost_conn_Spre s_post1' s_pre2) with
| mk_C_partial_post pre path1 =>
    Cpost_conn_Cpre_aux pre path1 c_pre2
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

Definition add_exp_to_Cpre b e 
  { s_pre : S_partial_pre }
  ( c_pre : C_partial_pre s_pre) := 
match s_pre with
| mk_S_partial_pre path =>
  match c_pre in C_partial_pre s_pre0
  return C_partial_pre (add_exp_to_Spre b e s_pre0) with
  | mk_C_partial_pre path  post =>
      mk_C_partial_pre (inl (b, e) :: path) post
  (* | bind_C_partial_pre A HA s_pre c_pre' =>
      bind_C_partial_pre A HA (add_exp_to_Spre e s_pre) 
        (fun a => add_exp_to_Cpre e (c_pre' a)) *)
  end
end.

Definition add_exp_to_Cpres b e 
  { s_pres : S_partial_pres }
  ( c_pres : C_partial_pres s_pres) := 
  Cmap (add_exp_to_Spre b e)
    (fun s_pre c_pre => @add_exp_to_Cpre b e s_pre c_pre) c_pres.

Definition add_P_to_Cpre P { s_pre } 
  (c_pre: C_partial_pre s_pre) : C_full_path (add_P_to_Spre s_pre) :=
match s_pre with
| mk_S_partial_pre path =>
  match c_pre in C_partial_pre path0
  return C_full_path (add_P_to_Spre path0) with
  | mk_C_partial_pre path Q =>
      mk_C_full_path P path Q
  end
end. 

Definition add_P_to_Cpres P {s_pres} 
  (c_pres: C_partial_pres s_pres) := 
  Cmap (add_P_to_Spre)
    (fun s_pre c_pre => @add_P_to_Cpre P s_pre c_pre) c_pres.


Fixpoint add_P_to_Catoms P s_atoms : C_partial_posts (add_P_to_atoms s_atoms) :=
  match s_atoms return C_partial_posts (add_P_to_atoms s_atoms) with
  | nil => list_binded_nil
  | cons (mk_atom path) s_atoms =>
      list_binded_cons 
        (mk_S_partial_post path )
        (mk_C_partial_post P path)
        (add_P_to_atoms s_atoms)
        (add_P_to_Catoms P s_atoms)
  end.
  
Fixpoint add_P_to_Catom_rets P s_atoms 
  : C_partial_post_rets (add_P_to_atom_rets s_atoms) :=
  match s_atoms return C_partial_post_rets (add_P_to_atom_rets s_atoms) with
  | nil => list_binded_nil
  | cons (mk_atom_ret path retval) s_atoms =>
      list_binded_cons 
        (mk_S_partial_post_ret path retval )
        (mk_C_partial_post_ret P path retval)
        (add_P_to_atom_rets s_atoms)
        (add_P_to_Catom_rets P s_atoms)
  end.
  
Definition add_Q_to_Cpost Q {s_post} 
  (c_post: C_partial_post s_post):
     C_full_path (add_Q_to_Spost s_post):=
match s_post with
| mk_S_partial_post path =>
  match c_post with
  | mk_C_partial_post P path =>
      mk_C_full_path P path Q
  end
end.

Definition add_Q_to_Cposts Q {s_posts} 
  (c_posts: C_partial_posts s_posts) := 
  Cmap (add_Q_to_Spost)
    (fun s_post c_post => @add_Q_to_Cpost Q s_post c_post) c_posts.


(* Definition add_Q_to_Catom Q { s_atom } : C_partial_pre (add_Q_to_atom s_atom) :=
  match s_atom with
  | mk_atom path =>
      mk_C_partial_pre path Q
  end. *)

Fixpoint add_Q_to_Catoms Q s_atoms : C_partial_pres (add_Q_to_atoms s_atoms) :=
  match s_atoms return C_partial_pres (add_Q_to_atoms s_atoms) with
  | nil => list_binded_nil
  | cons (mk_atom path) s_atoms =>
      list_binded_cons 
        (mk_S_partial_pre path)
        (mk_C_partial_pre path Q)
        (add_Q_to_atoms s_atoms)
        (add_Q_to_Catoms Q s_atoms)
  end.

(***********************************)
(** Simple result makers *)
(***********************************)

Definition S_split_sequence res1 res2 := 
  match res1 with
  |  Some (mk_S_result_rec s_pre1 s_path1 
        s_post_normal1 s_post_break1 s_post_continue1 s_post_return1
        s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1) =>
    match res2 with
    | Some (mk_S_result_rec s_pre2 s_path2 
          s_post_normal2 s_post_break2 s_post_continue2 s_post_return2
          s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2) =>
      Some (mk_S_result_rec
      (* S_pre *)
        (Sapp (s_pre1)  (atoms_conn_Spres s_atom_normal1 s_pre2))
      (* S_path *)
        (s_path1 +/+ s_path2 +/+ 
          Sposts_conn_Spres s_post_normal1 s_pre2)
      (* S_post_normal *)
        (s_post_normal2 +/+ 
          Sposts_conn_atoms s_post_normal1 s_atom_normal2)
      (* S_post_break *)
        (s_post_break1 +/+ s_post_break2 +/+ 
          Sposts_conn_atoms s_post_normal1 s_atom_break2)
      (* S_post_continue *)
        (s_post_continue1 +/+ s_post_continue2 +/+ 
          Sposts_conn_atoms s_post_normal1 s_atom_continue2)
      (* S_post_return *)
        (s_post_return1 +/+ s_post_return2 +/+ 
          Sposts_conn_returns s_post_normal1 s_atom_return2)
      (* S_atom_normal *)
        (atoms_conn_atoms s_atom_normal1 s_atom_normal2)
      (* S_atom_break *)
        (s_atom_break1 +/+
          atoms_conn_atoms s_atom_normal1 s_atom_break2)
      (* S_atom_continue *)
        (s_atom_continue1 +/+
          atoms_conn_atoms s_atom_normal1 s_atom_continue2)
      (* S_atom_return *)
        (s_atom_return1 +/+
          atoms_conn_returns s_atom_normal1 s_atom_return2))%aclight
    | None => None
    end
  | None => None
  end.



Definition S_split_ifthenelse (e: expr) res1 res2 := 
  match res1 with
  | Some (mk_S_result_rec s_pre1 s_path1 
        s_post_normal1 s_post_break1 s_post_continue1 s_post_return1
        s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1) =>
    match res2 with
    | Some (mk_S_result_rec s_pre2 s_path2 
          s_post_normal2 s_post_break2 s_post_continue2 s_post_return2
          s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2) =>
      Some (mk_S_result_rec 
      (* S_pre *)
        (add_exp_to_Spres true e s_pre1 +/+ add_exp_to_Spres false e s_pre2)
      (* S_path *)
        (s_path1 +/+ s_path2)
      (* S_post_normal *)
        (s_post_normal1 +/+ s_post_normal2)
      (* S_post_break *)
        (s_post_break1 +/+ s_post_break2)
      (* S_post_continue *)
        (s_post_continue1 +/+ s_post_continue2)
      (* S_post_return *)
        (s_post_return1 +/+ s_post_return2)
      (* S_atom_normal *)
        (add_exp_to_atoms true e s_atom_normal1 +/+
          add_exp_to_atoms false e s_atom_normal2)
      (* S_atom_break *)
        (add_exp_to_atoms true e s_atom_break1 +/+
          add_exp_to_atoms false e s_atom_break2)     
      (* S_atom_continue *)
        (add_exp_to_atoms true e s_atom_continue1 +/+
          add_exp_to_atoms false e s_atom_continue2)
      (* S_atom_return *)
        (add_exp_to_ret_atoms true e s_atom_return1 +/+
        add_exp_to_ret_atoms false e s_atom_return2))
    | None => None
    end
  | None => None
  end.


Definition S_split_loop res1 res2 := 
  match res1 with
  | Some (mk_S_result_rec s_pre1 s_path1 
        s_post_normal1 s_post_break1 s_post_continue1 s_post_return1
        s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1) =>
    match res2 with
    | Some (mk_S_result_rec s_pre2 s_path2 
          s_post_normal2 s_post_break2 s_post_continue2 s_post_return2
          s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2) =>
      Some (mk_S_result_rec 
      (* S_pre *)
        (s_pre1 +/+ atoms_conn_Spres s_atom_normal1 s_pre2 +/+ 
          atoms_conn_Spres s_atom_continue1 s_pre2 +/+ 
          atoms_conn_Spres s_atom_normal1
            (add_Q_to_atoms s_atom_continue2) +/+ 
          atoms_conn_Spres s_atom_continue1
            (add_Q_to_atoms s_atom_continue2))
      (* S_path *)
        (s_path1 +/+ s_path2 +/+ 
          Sposts_conn_Spres s_post_normal1 s_pre2 +/+ 
          Sposts_conn_Spres s_post_continue1 s_pre2 +/+ 
          Sposts_conn_Spres s_post_normal2 s_pre1 +/+ 
          Sposts_conn_Spres s_post_normal1
            (atoms_conn_Spres s_atom_normal2 s_pre1) +/+ 
          Sposts_conn_Spres s_post_continue1
            (atoms_conn_Spres s_atom_normal2 s_pre1) +/+ 
          Sposts_conn_Spres 
            (Sposts_conn_atoms s_post_normal2 s_atom_normal1)
            s_pre2 +/+ 
          Sposts_conn_Spres 
            (Sposts_conn_atoms s_post_normal2 s_atom_continue1)
            s_pre2 +/+ 
          Sposts_conn_Spres
            (Sposts_conn_atoms s_post_normal2 s_atom_normal1)
            (add_Q_to_atoms s_atom_continue2) +/+ 
          Sposts_conn_Spres
            (Sposts_conn_atoms s_post_normal2 s_atom_continue1)
            (add_Q_to_atoms s_atom_continue2) +/+ 
          Sposts_conn_Spres s_post_normal1
            (add_Q_to_atoms s_atom_continue2) +/+ 
          Sposts_conn_Spres s_post_continue1
            (add_Q_to_atoms s_atom_continue2) +/+ 
          add_Q_to_Sposts s_post_continue2)
      (* S_post_normal *)
        (s_post_break1 +/+ s_post_break2 +/+ 
          Sposts_conn_atoms s_post_normal1 s_atom_break2 +/+ 
          Sposts_conn_atoms s_post_normal2 s_atom_break1 +/+ 
          Sposts_conn_atoms s_post_continue1 s_atom_break2 +/+ 
          Sposts_conn_atoms
            (Sposts_conn_atoms s_post_normal2 s_atom_normal1)
            s_atom_break2 +/+ 
          Sposts_conn_atoms 
            (Sposts_conn_atoms s_post_normal2 s_atom_continue1)
            s_atom_break2 +/+ 
          Sposts_conn_atoms s_post_normal1
            (atoms_conn_atoms s_atom_normal2 s_atom_break1) +/+ 
          Sposts_conn_atoms s_post_continue1
            (atoms_conn_atoms s_atom_normal2 s_atom_break1))
      (* S_post_break *)    []
      (* S_post_continue *) []
      (* S_post_return *)
        (s_post_return1 +/+ s_post_return2 +/+ 
          Sposts_conn_returns s_post_normal1 s_atom_return2 +/+ 
          Sposts_conn_returns s_post_continue1 s_atom_return2 +/+ 
          Sposts_conn_returns s_post_normal2 s_atom_return1 +/+ 
          Sposts_conn_returns 
            (Sposts_conn_atoms s_post_normal2 s_atom_normal1)
            s_atom_return2 +/+ 
          Sposts_conn_returns 
            (Sposts_conn_atoms s_post_normal2 s_atom_continue1)
            s_atom_return2 +/+ 
          Sposts_conn_returns s_post_normal1 
            (atoms_conn_returns s_atom_normal2 s_atom_return1) +/+ 
          Sposts_conn_returns s_post_continue1 
            (atoms_conn_returns s_atom_normal2 s_atom_return1))
      (* S_atom_normal *)
        (s_atom_break1 +/+
          atoms_conn_atoms s_atom_normal1 s_atom_break2 +/+
          atoms_conn_atoms s_atom_continue1 s_atom_break2)
      (* S_atom_break *)    []
      (* S_atom_continue *) []
      (* S_atom_return *)
        (s_atom_return1 +/+
          atoms_conn_returns s_atom_normal1 s_atom_return2 +/+ 
          atoms_conn_returns s_atom_continue1 s_atom_return2 ))
      (* ) else None *)
      (* end *)
    | None => None
    end
  | None => None
  end.


Definition S_split_loop_refined (res1 res2: S_result) := 
  match res1, res2 with
  | Some (mk_S_result_rec s_pre1 s_path1 
        s_post_normal1 s_post_break1 s_post_continue1 s_post_return1
        s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1),
      Some (mk_S_result_rec s_pre2 s_path2 
        s_post_normal2 s_post_break2 s_post_continue2 s_post_return2
        s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2) =>
    match s_atom_normal2 with
    | nil =>  S_split_loop res1 res2
    | _ :: _  =>
      match s_atom_normal1 with
      | nil => 
        match s_atom_continue1 with
        | nil => S_split_loop res1 res2
        | _ :: _ => None
        end
      | _ :: _ => None
      end
    end
  | _, _ => None
  end.



Definition S_split_assert := 
  Some (mk_S_result_rec 
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
  ).


Definition S_split_skip := 
  Some (mk_S_result_rec 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   [ mk_atom nil ]
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
  ).


Definition S_split_assign (e1 e2: expr) := 
  Some (mk_S_result_rec 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   [ mk_atom [inr (Aassign e1 e2)] ]
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
  ).


Definition S_split_call 
  (id: option ident) (e: expr) (args: list expr) := 
  Some (mk_S_result_rec 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   [ mk_atom [inr (Acall id e args)] ]
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
  ).


Definition S_split_set (id: ident) (e: expr) := 
  Some (mk_S_result_rec 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   [ mk_atom [inr (Aset id e)] ]
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
  ).


Definition S_split_break := 
  Some (mk_S_result_rec 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   []
  (* S_atom_break *)    [ mk_atom nil ]
  (* S_atom_continue *) []
  (* S_atom_return *)   []
  ).

Definition S_split_continue := 
  Some (mk_S_result_rec 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   []
  (* S_atom_break *)    []
  (* S_atom_continue *) [ mk_atom nil ]
  (* S_atom_return *)   []
  ).

Definition S_split_return (e: option expr) := 
  Some (mk_S_result_rec 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   []
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   [ mk_atom_ret nil e ]
  ).


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
  | Sloop s1 s2 => 
      let res1 := S_split s1 in
      let res2 := S_split s2 in
      S_split_loop_refined res1 res2
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
      xs (flatten_binds binder_intro xs (tl_of x xs res'))
end.


Definition assert_of_pre {A:Type} s_pre :
  (A -> C_partial_pre s_pre)
  -> (A -> assert) :=
  match s_pre with
  | mk_S_partial_pre path =>
    fun c_pre =>
    fun a => match (c_pre a) with
             | mk_C_partial_pre path post =>
              post
    end
  end.

Definition hd_assert_of_pre {A:Type} {s_pre s_pres} :
(A -> C_partial_pres (s_pre::s_pres))
-> (A -> assert) :=
match s_pre with
| mk_S_partial_pre path =>
  fun c_pres =>
  fun a => match (c_pres a) with
            | list_binded_cons
                (mk_S_partial_pre path)
                (mk_C_partial_pre path' post)
                s_pres c_pres' =>
            post
  end
end.


Fixpoint flatten_partial_pres_binds {A:Type}
  (s_pres: S_partial_pres)
  : ( A -> C_partial_pres s_pres)
  -> C_partial_pres s_pres :=
  match s_pres with
  | nil => fun _ => list_binded_nil
  | (mk_S_partial_pre path) :: s_pres' =>
     fun c_pres' =>
     (* let c_pre := hd_of (mk_S_partial_pre path) s_pres' c_pres' in *)
     let c_pres := tl_of (mk_S_partial_pre path) s_pres' c_pres' in
     let c_pre_ass := hd_assert_of_pre c_pres' in
     let new_c_pre := mk_C_partial_pre path (exp c_pre_ass) in
      list_binded_cons
        (mk_S_partial_pre path) new_c_pre
        s_pres' (flatten_partial_pres_binds s_pres' c_pres)
  end.

Fixpoint flatten_partial_posts_binds {A:Type}
  (s_posts: S_partial_posts)
  : ( A -> C_partial_posts s_posts)
  -> C_partial_posts s_posts :=
  match s_posts with
  | nil => fun _ => list_binded_nil
  | (mk_S_partial_post path) :: s_posts' =>
     fun c_posts' =>
     (* let c_post := hd_of (mk_S_partial_post path) s_posts' c_posts' in *)
     let c_posts := tl_of (mk_S_partial_post path) s_posts' c_posts' in
     let c_post_ass := hd_assert_of_post c_posts' in
     let new_c_post := mk_C_partial_post (exp c_post_ass) path  in
      (* (@exp assert (@LiftNatDed' mpostd Nveric) A c_post_ass) in *)
      list_binded_cons
        (mk_S_partial_post path) new_c_post
        s_posts' (flatten_partial_posts_binds s_posts' c_posts)
  end.

Definition assert_of_post_ret {A:Type} s_post_ret :
(A -> C_partial_post_ret s_post_ret)
-> (A -> assert) :=
match s_post_ret with
| mk_S_partial_post_ret path ret =>
  fun c_post_ret =>
  fun a => match (c_post_ret a) with
            | mk_C_partial_post_ret pre path ret =>
            pre
  end
end.

Definition hd_assert_of_post_ret {A:Type} {s_post s_post_rets} :
(A -> C_partial_post_rets (s_post::s_post_rets))
-> (A -> assert) :=
match s_post with
| mk_S_partial_post_ret path ret =>
  fun c_post_rets =>
  fun a => match (c_post_rets a) with
            | list_binded_cons
                (mk_S_partial_post_ret path ret)
                (mk_C_partial_post_ret pre path' ret')
                s_post_rets c_post_rets' =>
            pre
    end
end.


Fixpoint flatten_partial_post_rets_binds {A:Type}
  (s_post_rets: S_partial_post_rets)
  : ( A -> C_partial_post_rets s_post_rets)
  -> C_partial_post_rets s_post_rets :=
  match s_post_rets with
  | nil => fun _ => list_binded_nil
  | (mk_S_partial_post_ret path ret) :: s_post_rets' =>
     fun c_post_rets' =>
     (* let c_post := hd_of (mk_S_partial_post path) s_post_rets' c_post_rets' in *)
     let c_post_rets := tl_of (mk_S_partial_post_ret path ret) s_post_rets' c_post_rets' in
     let c_post_ass := hd_assert_of_post_ret c_post_rets' in
     let new_c_post := mk_C_partial_post_ret (exp c_post_ass) path ret  in
      (* (@exp assert (@LiftNatDed' mpostd Nveric) A c_post_ass) in *)
      list_binded_cons
        (mk_S_partial_post_ret path ret) new_c_post
        s_post_rets' (flatten_partial_post_rets_binds s_post_rets' c_post_rets)
  end.




(* Definition flatten_partial_post_rets_binds {A:Type}
  (s_posts: S_partial_post_rets)
  (c_posts': A -> C_partial_post_rets s_posts)
  : C_partial_post_rets s_posts :=
  flatten_binds (bind_C_partial_post_ret A) s_posts c_posts'. *)

Definition flatten_full_paths_binds {A:Type}
  (s_paths: S_full_paths)
  (c_paths': A -> C_full_paths s_paths)
  : C_full_paths s_paths :=
  flatten_binds (bind_C_full_path A) s_paths c_paths'.

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
  (Some (mk_S_result_rec s_pre s_path 
    s_post_normal s_post_break s_post_continue s_post_return
    s_atom_normal s_atom_break s_atom_continue s_atom_return)).


Definition C_result_proj_C_pre (A : Type) (c_res: A -> C_result s_res) : A -> C_partial_pres s_pre :=
  fun a =>
    match (c_res a) with
    | mk_C_result_rec C_pre _ _ _ _ _ =>
        C_pre
    end.

Definition C_result_proj_C_post_normal (A : Type) (c_res: A -> C_result s_res) : A -> C_partial_posts s_post_normal :=
  fun a =>
    match (c_res a) 
    with
    | mk_C_result_rec _ _ C_post_normal _ _ _ =>
    C_post_normal
    end.


Definition C_result_proj_C_post_break (A : Type) (c_res: A -> C_result s_res) : A -> C_partial_posts (s_post_break) :=
  fun a =>
    match (c_res a) 
    with
    | mk_C_result_rec _ _ _ c_post_break _ _ =>
      c_post_break
    end.

Definition C_result_proj_C_post_continue (A : Type) (c_res: A -> C_result s_res) : A -> C_partial_posts (s_post_continue):=
fun a =>
match (c_res a) 
with
| mk_C_result_rec _ _ _ _ c_post_continue _ =>
c_post_continue
end.

Definition C_result_proj_C_post_return (A : Type) (c_res: A -> C_result s_res) : A -> C_partial_post_rets (s_post_return) :=
fun a =>
match (c_res a)
with
| mk_C_result_rec  _ _ _ _ _ C_post_return =>
C_post_return
end.

Definition C_result_proj_C_path (A : Type) (c_res: A -> C_result s_res) : A -> C_full_paths (s_path) :=
fun a =>
match (c_res a)
with
| mk_C_result_rec _ C_path  _ _ _ _ =>
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
  mk_C_result_rec
  (* S_pre *)           [ mk_S_partial_pre nil ]
  (* S_path *)          []
  (* S_post_normal *)   [ mk_S_partial_post nil]
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   []
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
  (* C_pre *)           { (mk_C_partial_pre nil a) }
  (* C_path *)          {}
  (* C_post_normal *)   { mk_C_partial_post a nil }
  (* C_post_break *)    {}
  (* C_post_continue *) {}
  (* C_post_return *)   {}
.




Definition C_split_sequence 
(res1 res2 : S_result)
(* (c1: C_statement s1) (c2: C_statement s2) *)
: C_result (res1) ->
  C_result (res2) ->

  C_result ((S_split_sequence res1 res2))
  (* Prop *)
  :=
match res1, res2 with
| None, _ => fun _ _ => tt
| _, None => fun _ _ => tt
| Some (mk_S_result_rec s_pre1 s_path1 
  s_post_normal1 s_post_break1 s_post_continue1 s_post_return1 s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1),
  Some (mk_S_result_rec s_pre2 s_path2
   s_post_normal2 s_post_break2 s_post_continue2 s_post_return2 s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2) =>
  fun (c_res1: C_result (Some (mk_S_result_rec s_pre1 s_path1 
  s_post_normal1 s_post_break1 s_post_continue1 s_post_return1 s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1)))
   (c_res2: C_result (Some (mk_S_result_rec s_pre2 s_path2
  s_post_normal2 s_post_break2 s_post_continue2 s_post_return2 s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2))) =>
  match c_res1, c_res2 with
  mk_C_result_rec c_pre1 c_path1 c_post_normal1 
     c_post_break1 c_post_continue1 c_post_return1,
  mk_C_result_rec c_pre2 c_path2 c_post_normal2
      c_post_break2 c_post_continue2 c_post_return2 =>
    mk_C_result_rec
    (* S_pre *)
      (s_pre1 +/+ atoms_conn_Spres s_atom_normal1 s_pre2)
      (* S_path *)
      (s_path1 +/+ s_path2 +/+ 
      Sposts_conn_Spres s_post_normal1 s_pre2)
      (* S_post_normal *)
      (s_post_normal2 +/+ 
      Sposts_conn_atoms s_post_normal1 s_atom_normal2)
      (* S_post_break *)
      (s_post_break1 +/+ s_post_break2 +/+ 
      Sposts_conn_atoms s_post_normal1 s_atom_break2)
      (* S_post_continue *)
      (s_post_continue1 +/+ s_post_continue2 +/+ 
      Sposts_conn_atoms s_post_normal1 s_atom_continue2)
      (* S_post_return *)
      (s_post_return1 +/+ s_post_return2 +/+ 
      Sposts_conn_returns s_post_normal1 s_atom_return2)
    (* S_atom_normal *)
      (atoms_conn_atoms s_atom_normal1 s_atom_normal2)
    (* S_atom_break *)
      (s_atom_break1 +/+ 
        atoms_conn_atoms s_atom_normal1 s_atom_break2)
    (* S_atom_continue *)
      (s_atom_continue1 +/+ 
        atoms_conn_atoms s_atom_normal1 s_atom_continue2)
    (* S_atom_return *)
      (s_atom_return1 +/+ 
        atoms_conn_returns s_atom_normal1 s_atom_return2)
      (* C_pre *)
      (c_pre1 +++ atoms_conn_Cpres s_atom_normal1 c_pre2)
      (* C_path *)
        (c_path1 +++ c_path2 +++ 
          Cposts_conn_Cpres c_post_normal1 c_pre2)
      (* C_post_normal *)
        (c_post_normal2 +++ 
          Cposts_conn_atoms c_post_normal1 s_atom_normal2)
      (* C_post_break *)
        (c_post_break1 +++ c_post_break2 +++
          Cposts_conn_atoms c_post_normal1 s_atom_break2)
      (* C_post_continue *)
        (c_post_continue1 +++ c_post_continue2 +++ 
          Cposts_conn_atoms c_post_normal1 s_atom_continue2)
      (* C_post_return *)
        (c_post_return1 +++ c_post_return2 +++ 
          Cposts_conn_returns c_post_normal1 s_atom_return2)
  end
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


Fixpoint add_exP_to_Cpre {A:Type}
  (c_ass': A -> assert) {s_pres: S_partial_pres} :
  (A -> C_partial_pres s_pres)
  -> C_full_paths (Sposts_conn_Spres [(mk_S_partial_post nil)] s_pres) :=
  match s_pres 
  with
  | nil => fun _ => 
    (list_binded_nil : 
      C_full_paths (Sposts_conn_Spres [mk_S_partial_post []] []))
  | s_pre :: s_pres' =>
      fun c_pres =>
        list_binded_cons
          (Spost_conn_Spre (mk_S_partial_post nil) s_pre)
          (bind_C_full_path A (add_P_to_Spre s_pre) (fun a =>
            Cpost_conn_Cpre 
                (mk_C_partial_post (c_ass' a) nil)
                (hd_of s_pre s_pres' c_pres a)
          ))
          (Sposts_conn_Spres [mk_S_partial_post nil] s_pres')
          (add_exP_to_Cpre c_ass' (tl_of s_pre s_pres' c_pres))
end.


Definition C_split_exgiven (s_res: S_result) (A: Type) 
 (c_ass': A -> assert) : (A -> C_result s_res) ->
C_result (S_split_sequence S_split_assert s_res ) :=
match s_res with
| Some (mk_S_result_rec s_pre s_path s_post_normal s_post_break s_post_continue s_post_return s_atom_normal s_atom_break s_atom_continue s_atom_return) =>
fun (c_res': A -> C_result (Some (mk_S_result_rec s_pre s_path s_post_normal s_post_break s_post_continue s_post_return s_atom_normal s_atom_break s_atom_continue s_atom_return)))  =>
let ex_ass := exp c_ass' in
let c_pre := C_result_proj_C_pre A c_res' in
let c_post_normal := C_result_proj_C_post_normal A c_res' in
let c_post_normal := flatten_partial_posts_binds (s_post_normal) c_post_normal in
let c_post_break := C_result_proj_C_post_break A c_res' in
let c_post_break := flatten_partial_posts_binds (s_post_break) c_post_break in
let c_post_continue := C_result_proj_C_post_continue A c_res' in
let c_post_continue := flatten_partial_posts_binds (s_post_continue) c_post_continue in
let c_post_return := C_result_proj_C_post_return A c_res' in
let c_post_return := flatten_partial_post_rets_binds (s_post_return) c_post_return in
let c_path := C_result_proj_C_path A c_res' in
let c_path := flatten_full_paths_binds (s_path) c_path in

let ass_post_normal_C := 
          (* bind_C_partial_post A 
          (mk_S_partial_post nil)
          (fun a => mk_C_partial_post (c_ass' a) nil) in *)
          mk_C_partial_post (ex_ass) nil in
let ass_post_normal_S := mk_S_partial_post nil in

mk_C_result_rec
(* S_pre *)
  ( [ mk_S_partial_pre nil ])
(* S_path *)
  (s_path +/+ 
    (* add_P_to_Spres s_pre) *)
    Sposts_conn_Spres [ass_post_normal_S] s_pre)
(* S_post_normal *)
  (s_post_normal +/+ 
    Sposts_conn_atoms [ass_post_normal_S] s_atom_normal)
(* S_post_break *)
  (s_post_break +/+ 
    Sposts_conn_atoms [ass_post_normal_S] s_atom_break)
(* S_post_continue *)
  (s_post_continue +/+ 
    Sposts_conn_atoms [ass_post_normal_S] s_atom_continue)
(* S_post_return *)
  ( s_post_return +/+ 
    Sposts_conn_returns [ass_post_normal_S] s_atom_return)
(* S_atom_normal *)   []
(* S_atom_break *)    []
(* S_atom_continue *) []
(* S_atom_return *)   []
(* C_pre *)
( { mk_C_partial_pre nil ex_ass})
(* C_path *)
  (c_path +++
    add_exP_to_Cpre c_ass' c_pre)
    (* Cposts_conn_Cpres { ass_post_normal_C } c_pre) *)
(* C_post_normal *)
  (c_post_normal +++ 
    Cposts_conn_atoms { ass_post_normal_C } s_atom_normal)
(* C_post_break *)
  (c_post_break +++
    Cposts_conn_atoms { ass_post_normal_C } s_atom_break)
(* C_post_continue *)
  ( c_post_continue +++ 
    Cposts_conn_atoms { ass_post_normal_C } s_atom_continue)
(* C_post_return *)
  ( c_post_return +++ 
    Cposts_conn_returns { ass_post_normal_C } s_atom_return)


| None => fun _ => tt
end.


Definition C_split_skip : C_result (S_split Sskip) :=
  mk_C_result_rec 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   [ mk_atom nil ]
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
  (* C_pre *)           {}
  (* C_path *)          {}
  (* C_post_normal *)   {}
  (* C_post_normal *)   {}
  (* C_post_normal *)   {}
  (* C_post_normal *)   {}
.

Definition C_split_assign e1 e2 : C_result (S_split (Sassign e1 e2)) :=
  mk_C_result_rec 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   [ mk_atom [inr (Aassign e1 e2)] ]
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
  (* C_pre *)           {}
  (* C_path *)          {}
  (* C_post_normal *)   {}
  (* C_post_normal *)   {}
  (* C_post_normal *)   {}
  (* C_post_normal *)   {}
  .

Definition C_split_call id e args : C_result (S_split (Scall id e args)) :=
  mk_C_result_rec 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   [ mk_atom [inr (Acall id e args)] ]
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
  (* C_pre *)           {}
  (* C_path *)          {}
  (* C_post_normal *)   {}
  (* C_post_normal *)   {}
  (* C_post_normal *)   {}
  (* C_post_normal *)   {}
  .

Definition C_split_set e1 e2 : C_result (S_split (Sset e1 e2)) :=
  mk_C_result_rec 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   [ mk_atom [inr (Aset e1 e2)] ]
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   []
  (* C_pre *)           {}
  (* C_path *)          {}
  (* C_post_normal *)   {}
  (* C_post_normal *)   {}
  (* C_post_normal *)   {}
  (* C_post_normal *)   {}
  .

Definition C_split_break : C_result (S_split Sbreak) :=
  mk_C_result_rec 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   []
  (* S_atom_break *)    [ mk_atom nil ]
  (* S_atom_continue *) []
  (* S_atom_return *)   []
  (* C_pre *)           {}
  (* C_path *)          {}
  (* C_post_normal *)   {}
  (* C_post_break *)    {}
  (* C_post_continue *) {}
  (* C_post_return *)   {}
  .

Definition C_split_continue : C_result (S_split Scontinue) :=
  mk_C_result_rec 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   []
  (* S_atom_break *)    []
  (* S_atom_continue *) [ mk_atom nil]
  (* S_atom_return *)   []
  (* C_pre *)           {}
  (* C_path *)          {}
  (* C_post_normal *)   {}
  (* C_post_break *)    {}
  (* C_post_continue *) {}
  (* C_post_return *)   {}
  .

Definition C_split_return e : C_result (S_split (Sreturn e)) :=
  mk_C_result_rec 
  (* S_pre *)           []
  (* S_path *)          []
  (* S_post_normal *)   []
  (* S_post_break *)    []
  (* S_post_continue *) []
  (* S_post_return *)   []
  (* S_atom_normal *)   []
  (* S_atom_break *)    []
  (* S_atom_continue *) []
  (* S_atom_return *)   [ mk_atom_ret nil e ]
  (* C_pre *)           {}
  (* C_path *)          {}
  (* C_post_normal *)   {}
  (* C_post_break *)    {}
  (* C_post_continue *) {}
  (* C_post_return *)   {}
  .

Definition C_split_ifthenelse (e: expr)
(res1 res2 : S_result)
: C_result res1 ->
  C_result res2 ->
  C_result (S_split_ifthenelse e res1 res2) :=
match res1, res2 with
| None, _ => fun _ _ => tt
| _, None => fun _ _ => tt
| Some (mk_S_result_rec s_pre1 s_path1 
  s_post_normal1 s_post_break1 s_post_continue1 s_post_return1 s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1),
  Some (mk_S_result_rec s_pre2 s_path2
   s_post_normal2 s_post_break2 s_post_continue2 s_post_return2 s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2) =>
  fun c_res1 c_res2 =>
  match c_res1, c_res2 with
  mk_C_result_rec c_pre1 c_path1 c_post_normal1 
     c_post_break1 c_post_continue1 c_post_return1,
  mk_C_result_rec c_pre2 c_path2 c_post_normal2
      c_post_break2 c_post_continue2 c_post_return2 =>
    mk_C_result_rec
    (* S_pre *)
      (add_exp_to_Spres true e s_pre1 +/+ add_exp_to_Spres false e s_pre2)
    (* S_path *)
      (s_path1 +/+ s_path2)
    (* S_post_normal *)
      (s_post_normal1 +/+ s_post_normal2)
    (* S_post_break *)
      (s_post_break1 +/+ s_post_break2)
    (* S_post_continue *)
      (s_post_continue1 +/+ s_post_continue2)
    (* S_post_return *)
      (s_post_return1 +/+ s_post_return2)
    (* S_atom_normal *)
      (add_exp_to_atoms true e s_atom_normal1 +/+ 
        add_exp_to_atoms false e s_atom_normal2)
    (* S_atom_break *)
      (add_exp_to_atoms true e s_atom_break1 +/+ 
        add_exp_to_atoms false e s_atom_break2)     
    (* S_atom_continue *)
      (add_exp_to_atoms true e s_atom_continue1 +/+ 
        add_exp_to_atoms false e s_atom_continue2)
    (* S_atom_return *)
      (add_exp_to_ret_atoms true e s_atom_return1 +/+ 
      add_exp_to_ret_atoms false e s_atom_return2)
    (* C_pre *)
      (add_exp_to_Cpres true e c_pre1 +++ add_exp_to_Cpres false e c_pre2)
    (* C_path *)
      (c_path1 +++ c_path2)
    (* C_post_normal *)
      (c_post_normal1 +++ c_post_normal2)
    (* C_post_break *)
      (c_post_break1 +++ c_post_break2)
    (* C_post_continue *)
      (c_post_continue1 +++ c_post_continue2)
    (* C_post_return *)
      (c_post_return1 +++ c_post_return2)
  end
end.

Definition C_split_loop
(res1 res2 : S_result)
: C_result res1 ->
  C_result res2 ->
  C_result (S_split_loop res1 res2):=
match res1, res2 with
| None, _ => fun _ _ => tt
| _, None => fun _ _ => tt
| Some (mk_S_result_rec s_pre1 s_path1 
  s_post_normal1 s_post_break1 s_post_continue1 s_post_return1 s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1),
  Some (mk_S_result_rec s_pre2 s_path2
   s_post_normal2 s_post_break2 s_post_continue2 s_post_return2 s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2) =>
  fun c_res1 c_res2 =>
  match c_res1, c_res2 with
  mk_C_result_rec c_pre1 c_path1 c_post_normal1 
     c_post_break1 c_post_continue1 c_post_return1,
  mk_C_result_rec c_pre2 c_path2 c_post_normal2
      c_post_break2 c_post_continue2 c_post_return2 =>

    mk_C_result_rec 
    (* S_pre *)
      (s_pre1 +/+ atoms_conn_Spres s_atom_normal1 s_pre2 +/+ 
        atoms_conn_Spres s_atom_continue1 s_pre2 +/+ 
        atoms_conn_Spres s_atom_normal1
            (add_Q_to_atoms s_atom_continue2) +/+ 
        atoms_conn_Spres s_atom_continue1
          (add_Q_to_atoms s_atom_continue2))
    (* S_path *)
      (s_path1 +/+ s_path2 +/+ 
        Sposts_conn_Spres s_post_normal1 s_pre2 +/+ 
        Sposts_conn_Spres s_post_continue1 s_pre2 +/+ 
        Sposts_conn_Spres s_post_normal2 s_pre1 +/+ 
        Sposts_conn_Spres s_post_normal1
          (atoms_conn_Spres s_atom_normal2 s_pre1) +/+ 
        Sposts_conn_Spres s_post_continue1
          (atoms_conn_Spres s_atom_normal2 s_pre1) +/+ 
        Sposts_conn_Spres 
          (Sposts_conn_atoms s_post_normal2 s_atom_normal1)
          s_pre2 +/+ 
        Sposts_conn_Spres 
          (Sposts_conn_atoms s_post_normal2 s_atom_continue1)
          s_pre2 +/+ 
        Sposts_conn_Spres
          (Sposts_conn_atoms s_post_normal2 s_atom_normal1)
          (add_Q_to_atoms s_atom_continue2) +/+ 
        Sposts_conn_Spres
          (Sposts_conn_atoms s_post_normal2 s_atom_continue1)
          (add_Q_to_atoms s_atom_continue2) +/+ 
        Sposts_conn_Spres s_post_normal1
          (add_Q_to_atoms s_atom_continue2) +/+ 
        Sposts_conn_Spres s_post_continue1
          (add_Q_to_atoms s_atom_continue2) +/+ 
        add_Q_to_Sposts s_post_continue2)
    (* S_post_normal *)
      (s_post_break1 +/+ s_post_break2 +/+ 
        Sposts_conn_atoms s_post_normal1 s_atom_break2 +/+ 
        Sposts_conn_atoms s_post_normal2 s_atom_break1 +/+ 
        Sposts_conn_atoms s_post_continue1 s_atom_break2 +/+ 
        Sposts_conn_atoms
          (Sposts_conn_atoms s_post_normal2 s_atom_normal1)
          s_atom_break2 +/+ 
        Sposts_conn_atoms 
          (Sposts_conn_atoms s_post_normal2 s_atom_continue1)
          s_atom_break2 +/+ 
        Sposts_conn_atoms s_post_normal1
          (atoms_conn_atoms s_atom_normal2 s_atom_break1) +/+ 
        Sposts_conn_atoms s_post_continue1
          (atoms_conn_atoms s_atom_normal2 s_atom_break1))
    (* S_post_break *)    []
    (* S_post_continue *) []
    (* S_post_return *)
      (s_post_return1 +/+ s_post_return2 +/+ 
        Sposts_conn_returns s_post_normal1 s_atom_return2 +/+ 
        Sposts_conn_returns s_post_continue1 s_atom_return2 +/+ 
        Sposts_conn_returns s_post_normal2 s_atom_return1 +/+ 
        Sposts_conn_returns 
          (Sposts_conn_atoms s_post_normal2 s_atom_normal1)
          s_atom_return2 +/+ 
        Sposts_conn_returns 
          (Sposts_conn_atoms s_post_normal2 s_atom_continue1)
          s_atom_return2 +/+ 
        Sposts_conn_returns s_post_normal1 
          (atoms_conn_returns s_atom_normal2 s_atom_return1) +/+ 
        Sposts_conn_returns s_post_continue1 
          (atoms_conn_returns s_atom_normal2 s_atom_return1))
    (* S_atom_normal *)
      (s_atom_break1 +/+ 
        atoms_conn_atoms s_atom_normal1 s_atom_break2 +/+ 
        atoms_conn_atoms s_atom_continue1 s_atom_break2)
    (* S_atom_break *)    []
    (* S_atom_continue *) []
    (* S_atom_return *)
      (s_atom_return1 +/+ 
        atoms_conn_returns s_atom_normal1 s_atom_return2 +/+ 
        atoms_conn_returns s_atom_continue1 s_atom_return2 )
    (* C_pre *)
      (c_pre1 +++ atoms_conn_Cpres s_atom_normal1 c_pre2 +++
        atoms_conn_Cpres s_atom_continue1 c_pre2 +++
        atoms_conn_Cpres s_atom_normal1
            (add_Q_to_Catoms seplog.FF s_atom_continue2) +++
        atoms_conn_Cpres s_atom_continue1
          (add_Q_to_Catoms seplog.FF s_atom_continue2))
    (* C_path *)
      (c_path1 +++ c_path2 +++
        Cposts_conn_Cpres c_post_normal1 c_pre2 +++
        Cposts_conn_Cpres c_post_continue1 c_pre2 +++
        Cposts_conn_Cpres c_post_normal2 c_pre1 +++
        Cposts_conn_Cpres c_post_normal1
          (atoms_conn_Cpres s_atom_normal2 c_pre1) +++
        Cposts_conn_Cpres c_post_continue1
          (atoms_conn_Cpres s_atom_normal2 c_pre1) +++
        Cposts_conn_Cpres 
          (Cposts_conn_atoms c_post_normal2 s_atom_normal1)
          c_pre2 +++
        Cposts_conn_Cpres 
          (Cposts_conn_atoms c_post_normal2 s_atom_continue1)
          c_pre2 +++
        Cposts_conn_Cpres
          (Cposts_conn_atoms c_post_normal2 s_atom_normal1)
          (add_Q_to_Catoms seplog.FF s_atom_continue2) +++
        Cposts_conn_Cpres
          (Cposts_conn_atoms c_post_normal2 s_atom_continue1)
          (add_Q_to_Catoms seplog.FF s_atom_continue2) +++
        Cposts_conn_Cpres c_post_normal1
          (add_Q_to_Catoms seplog.FF s_atom_continue2) +++
        Cposts_conn_Cpres c_post_continue1
          (add_Q_to_Catoms seplog.FF s_atom_continue2) +++
        add_Q_to_Cposts seplog.FF c_post_continue2)
    (* C_post_normal *)
      (c_post_break1 +++ c_post_break2 +++
        Cposts_conn_atoms c_post_normal1 s_atom_break2 +++
        Cposts_conn_atoms c_post_normal2 s_atom_break1 +++
        Cposts_conn_atoms c_post_continue1 s_atom_break2 +++
        Cposts_conn_atoms
          (Cposts_conn_atoms c_post_normal2 s_atom_normal1)
          s_atom_break2 +++
        Cposts_conn_atoms 
          (Cposts_conn_atoms c_post_normal2 s_atom_continue1)
          s_atom_break2 +++
        Cposts_conn_atoms c_post_normal1
          (atoms_conn_atoms s_atom_normal2 s_atom_break1) +++
        Cposts_conn_atoms c_post_continue1
          (atoms_conn_atoms s_atom_normal2 s_atom_break1))
    (* C_post_break *)    {}
    (* C_post_continue *) {}
    (* C_post_return *)
      (c_post_return1 +++ c_post_return2 +++
      Cposts_conn_returns c_post_normal1 s_atom_return2 +++
      Cposts_conn_returns c_post_continue1 s_atom_return2 +++
      Cposts_conn_returns c_post_normal2 s_atom_return1 +++
      Cposts_conn_returns 
        (Cposts_conn_atoms c_post_normal2 s_atom_normal1)
        s_atom_return2 +++
      Cposts_conn_returns 
        (Cposts_conn_atoms c_post_normal2 s_atom_continue1)
        s_atom_return2 +++
      Cposts_conn_returns c_post_normal1 
        (atoms_conn_returns s_atom_normal2 s_atom_return1) +++
      Cposts_conn_returns c_post_continue1 
        (atoms_conn_returns s_atom_normal2 s_atom_return1))
      end
end.

Definition C_split_loop_refined
(res1 res2 : S_result)
: C_result res1 ->
  C_result res2 ->
  C_result (S_split_loop_refined res1 res2):=
match res1, res2 with
| None, _ => fun _ _ => tt
| _, None => fun _ _ => tt
| Some (mk_S_result_rec s_pre1 s_path1 
      s_post_normal1 s_post_break1 s_post_continue1 s_post_return1
      s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1),
  Some (mk_S_result_rec s_pre2 s_path2 
    s_post_normal2 s_post_break2 s_post_continue2 s_post_return2
    s_atom_normal2 s_atom_break2 s_atom_continue2 s_atom_return2) =>

    match s_atom_normal2 with
    | nil =>
      fun c_res1 c_res2 => 
      C_split_loop
        (Some (mk_S_result_rec s_pre1 s_path1 
          s_post_normal1 s_post_break1 s_post_continue1 s_post_return1
          s_atom_normal1 s_atom_break1 s_atom_continue1 s_atom_return1))
        (Some (mk_S_result_rec s_pre2 s_path2 
          s_post_normal2 s_post_break2 s_post_continue2 s_post_return2
          nil s_atom_break2 s_atom_continue2 s_atom_return2))
        c_res1 c_res2
    | s_atom_normal2a :: s_atom_normal2b =>
      match s_atom_normal1, s_atom_continue1 with
      | nil, nil =>
          fun c_res1 c_res2 => 
            C_split_loop 
              (Some (mk_S_result_rec s_pre1 s_path1 
                s_post_normal1 s_post_break1 s_post_continue1 s_post_return1
                nil s_atom_break1 nil s_atom_return1))
              (Some (mk_S_result_rec s_pre2 s_path2 
                s_post_normal2 s_post_break2 s_post_continue2 s_post_return2
                (s_atom_normal2a :: s_atom_normal2b) s_atom_break2 s_atom_continue2 s_atom_return2))
              c_res1 c_res2
      | _, _ => fun _ _ => tt
      end
    end
end.


Fixpoint C_split (s: S_statement) (c: C_statement s) : C_result (S_split s) :=
match c as c0 in C_statement s0
  return C_result (S_split s0)
with
| Csequence s1 s2 c1 c2 =>
    C_split_sequence (S_split s1) (S_split s2)
     (C_split s1 c1) (C_split s2 c2)
| Cassert a =>
    C_split_assert a
| Cskip => 
    C_split_skip
| Cexgiven A ass c a_stm' =>
    C_split_exgiven (S_split c) A ass
      (fun a =>  C_split c (a_stm' a))
| Cassign e1 e2 =>
    C_split_assign e1 e2
| Ccall id e args =>
    C_split_call id e args
| Cset id e =>
    C_split_set id e
| Cifthenelse e s1 s2 c1 c2 =>
    C_split_ifthenelse e (S_split s1) (S_split s2)
    (C_split s1 c1) (C_split s2 c2)
| Cloop s1 s2 c1 c2 =>
    C_split_loop_refined (S_split s1) (S_split s2) (C_split s1 c1) (C_split s2 c2)
| Cbreak =>
    C_split_break
| Ccontinue =>
    C_split_continue
| Creturn e =>
    C_split_return e
end.


Close Scope aclight_scope.
Bind Scope list_scope with list.


Lemma S_split_eq: forall s, S_split s = AClight.S_split s.
Proof. intros. reflexivity. Qed.
Lemma C_split_eq: forall s c, C_split s c = AClight.C_split s c.
Proof. intros. reflexivity. Qed.
