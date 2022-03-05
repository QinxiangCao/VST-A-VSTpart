Require Import Split.AClight2.
Require Import VST.floyd.proofauto.
Require Import Split.vst_ext.
Notation "x ;; y" := (Ssequence x y)  (at level 65) : logic.
Require Import VST.veric.semax_lemmas.

Module Split.


Definition option_map2 {A B C:Type} (f:A->B->C) (o1 : option A) (o2 : option B) : option C :=
  match o1, o2 with
    | Some a, Some b => @Some C (f a b)
    | _, _ => @None C
  end.

Definition option_app {A:Type} := option_map2 (@app A).



Inductive atom_statement : Type :=
| ASskip : atom_statement                   (**r do nothing *)
| ASassign : expr -> expr -> atom_statement (**r assignment [lvalue = rvalue] *)
| ASset : ident -> expr -> atom_statement   (**r assignment [tempvar = rvalue] *)
| AScall: option ident -> expr 
            -> list expr -> atom_statement   (**r function call *).

Definition path:= list (expr + atom_statement) .



(****************************************
****************************************
****************************************
       Basic Type Definitions
****************************************
****************************************
***************************************)

(* 

{ EX x. P(x) }
Given x...

{ Q(x) }




*)

Inductive path_statement : Type :=
| path_intro (pre:assert) (path:path) (post:assert)
| path_binded (A:Type) (HA: inhabited A) : (A -> path_statement) -> path_statement.



Inductive path_statements : Type :=
| path_statements_nil
| path_statements_cons (st:path_statement) (sts:path_statements)
| path_statementsbinded (A:Type) (HA: inhabited A) : (A -> path_statements) -> path_statements.

      



Inductive partial_pre_statement : Type :=
| partial_pre_intro (path:path) (post:assert)
| partial_pre_binded (A:Type) (HA: inhabited A) : (A -> partial_pre_statement) -> partial_pre_statement.

Inductive partial_post_statement : Type :=
| partial_post_intro (pre:assert) (path:path)
| partial_post_binded (A:Type) (HA: inhabited A) : (A -> partial_post_statement) -> partial_post_statement.

Inductive partial_return_statement : Type :=
| partial_return_intro (pre:assert) (path:path) (retval: option expr)
| partial_return_binded (A:Type) (HA: inhabited A) : (A -> partial_return_statement) -> partial_return_statement.

Inductive atom_normal_statement: Type :=
| atom_normal_intro (path: path).

Inductive atom_return_statement: Type :=
| atom_return_intro (path: path) (retval: option expr).  


Record split_result_basic: Type := Pack{
  pre   : list partial_pre_statement; (* no more binded pres with ex-given *)
  paths : list path_statement;
  normal_post  : list partial_post_statement;
  continue_post: list partial_post_statement;
  break_post   : list partial_post_statement;
  return_post  : list partial_return_statement;
  normal_atom  : list atom_normal_statement;
  continue_atom: list atom_normal_statement;
  break_atom   : list atom_normal_statement;
  return_atom  : list atom_return_statement;
}.


(*****************************)
(*****************************)
(* Basic Operations on paths *)
(*****************************)
(*****************************)
Fixpoint add_P_to_partial_pre P pre := match pre with
| partial_pre_intro path Q => path_intro P path Q
| partial_pre_binded A HA pre' =>
    path_binded A HA (fun x =>
      add_P_to_partial_pre P (pre' x)
    )
end.

Definition add_P_to_partial_pres P := map (add_P_to_partial_pre P).

Definition add_P_to_normal_atom P atom := match atom with
| atom_normal_intro path => partial_post_intro P path end.

Definition add_P_to_normal_atoms P := map (add_P_to_normal_atom P).

Definition add_P_to_return_atom P atom := match atom with
| atom_return_intro path retval => partial_return_intro P path retval end.

Definition add_P_to_return_atoms P := map (add_P_to_return_atom P).

Fixpoint add_Q_to_normal_post Q post := match post with
| partial_post_intro P path => path_intro P path Q
| partial_post_binded A HA post' =>
    path_binded A HA (fun x => add_Q_to_normal_post Q (post' x))
end.

Definition add_Q_to_normal_posts posts Q := map (add_Q_to_normal_post Q) posts.

Definition add_Q_to_normal_atom Q atom := match atom with
| atom_normal_intro path => partial_pre_intro path Q end.

Definition add_Q_to_normal_atoms atoms Q := map (add_Q_to_normal_atom Q) atoms.

Fixpoint add_bexp_to_partial_pre bexp pre := match pre with
| partial_pre_intro path Q => partial_pre_intro ((inl bexp)::path) Q
| partial_pre_binded A HA pre' =>
    partial_pre_binded A HA 
      (fun x => add_bexp_to_partial_pre bexp (pre' x))
end.

Definition add_bexp_to_partial_pres bexp := map (add_bexp_to_partial_pre bexp).

Definition add_bexp_to_normal_atom bexp atom := match atom with
| atom_normal_intro path => atom_normal_intro ((inl bexp)::path) end.

Definition add_bexp_to_normal_atoms bexp := map (add_bexp_to_normal_atom bexp).

Definition add_bexp_to_return_atom bexp atom := match atom with
| atom_return_intro path retval => atom_return_intro ((inl bexp)::path) retval end.

Definition add_bexp_to_return_atoms bexp := map (add_bexp_to_return_atom bexp).

Fixpoint product_map {A B C: Type} (f: A -> B -> C) (xs: list A) (ys: list B) : list C :=
  concat (map (fun x => map (f x) ys) xs).

Fixpoint atom_conn_pre atom pre : partial_pre_statement :=
  match atom with atom_normal_intro p1 =>
    match pre with 
    | partial_pre_intro p2 Q =>
        partial_pre_intro (p1 ++ p2) Q 
    | partial_pre_binded A HA pre' =>
        partial_pre_binded A HA (fun x => atom_conn_pre atom (pre' x))
    end
  end.

Definition atoms_conn_pres := option_map2 (product_map atom_conn_pre).

Definition atom_conn_atom atom1 atom2 : atom_normal_statement :=
  match atom1 with atom_normal_intro p1 =>
    match atom2 with atom_normal_intro p2 =>
    atom_normal_intro (p1 ++ p2) end
  end.

Definition atoms_conn_atoms := option_map2 (product_map atom_conn_atom).

Definition atom_conn_return atom1 atom2 : atom_return_statement :=
  match atom1 with atom_normal_intro p1 =>
    match atom2 with atom_return_intro p2 rv =>
    atom_return_intro (p1 ++ p2) rv end
  end.

Definition atoms_conn_returns := option_map2 (product_map atom_conn_return).

Fixpoint post_conn_atom post atom : partial_post_statement :=
  match post with 
  | partial_post_intro P p1 =>
    match atom with atom_normal_intro p2 =>
      partial_post_intro P (p1 ++ p2) end
  | partial_post_binded A HA post' =>
      partial_post_binded A HA 
        (fun x => post_conn_atom (post' x) atom )
  end.

Definition posts_conn_atoms := option_map2 (product_map post_conn_atom).

Fixpoint post_conn_return post atom : partial_return_statement :=
  match post with
  | partial_post_intro P p1 =>
    match atom with atom_return_intro p2 rv =>
      partial_return_intro P (p1 ++ p2) rv end
  | partial_post_binded A HA post' =>
      partial_return_binded A HA 
        (fun x => post_conn_return (post' x) atom)
  end.

Definition posts_conn_returns := option_map2 (product_map post_conn_return).
  

Fixpoint post_conn_pre_aux P p1 pre : path_statement :=
  match pre with
  | partial_pre_intro p2 Q =>
      path_intro P (p1 ++ p2) Q 
  | partial_pre_binded A HA pre' =>
      path_binded A HA (fun x => post_conn_pre_aux P p1 (pre' x))
  end.

Fixpoint post_conn_pre post pre : path_statement :=
  match post with 
  | partial_post_intro P p1 =>
      post_conn_pre_aux P p1 pre
  | partial_post_binded A HA post' =>
      path_binded A HA (fun x => post_conn_pre (post' x) pre)
  end.

Definition posts_conn_pres := option_map2 (product_map post_conn_pre).

  

(*****************************)
(*****************************)
(* Combinations for language constructs *)
(*****************************)
(*****************************)

(**********************************************)
(* combine a ex-given pre-condition to a split-result
   Ppre = EX a:A. P(a)
   P = P(a)
   res = res(a) *)
(**********************************************)

Definition add_given_P_to_basic_result Ppre P res := {|
  pre          := [ partial_pre_intro [] Ppre  ];
  paths        := paths res ++ List.map (add_P_to_partial_pre P) (pre res);
  normal_post  := normal_post res ++ List.map (add_P_to_normal_atom P) (normal_atom res);
  continue_post:= continue_post res ++ List.map (add_P_to_normal_atom P) (continue_atom res);
  break_post   := break_post res ++ List.map (add_P_to_normal_atom P) (break_atom res);
  return_post  := return_post res ++ List.map (add_P_to_return_atom P) (return_atom res);
  normal_atom  := [] ;
  continue_atom:= [] ;
  break_atom   := [] ;
  return_atom  := [] ;
|}.

(**********************************************)
(* split results for baisc language structures *)
(**********************************************)

Definition Sskip_split := {|
  pre          := [] ;
  paths        := [] ;
  normal_post  := [] ;
  continue_post:= [] ;
  break_post   := [] ;
  return_post  := [] ;
  normal_atom  := [ atom_normal_intro [] ] ;
  continue_atom:= [] ;
  break_atom   := [] ;
  return_atom  := [] ;
|}.

Definition Sassert_split a := {|
  pre          := [ partial_pre_intro [] a ] ;
  paths        := [] ;
  normal_post  := [ partial_post_intro a [] ] ;
  continue_post:= [] ;
  break_post   := [] ;
  return_post  := [] ;
  normal_atom  := [] ;
  continue_atom:= [] ;
  break_atom   := [] ;
  return_atom  := [] ;
|}.

Definition Sassign_split e1 e2 := {|
  pre          := [] ;
  paths        := [] ;
  normal_post  := [] ;
  continue_post:= [] ;
  break_post   := [] ;
  return_post  := [] ;
  normal_atom  := [ atom_normal_intro [ inr (ASassign e1 e2) ] ] ;
  continue_atom:= [] ;
  break_atom   := [] ;
  return_atom  := [] ;
|}.

Definition Sset_split i e := {|
  pre          := [] ;
  paths        := [] ;
  normal_post  := [] ;
  continue_post:= [] ;
  break_post   := [] ;
  return_post  := [] ;
  normal_atom  := [ atom_normal_intro [ inr (ASset i e) ] ] ;
  continue_atom:= [] ;
  break_atom   := [] ;
  return_atom  := [] ;
|}.


Definition Sbreak_split := {|
  pre          := [] ;
  paths        := [] ;
  normal_post  := [] ;
  continue_post:= [] ;
  break_post   := [] ;
  return_post  := [] ;
  normal_atom  := [] ;
  continue_atom:= [] ;
  break_atom   := [ atom_normal_intro [] ] ;
  return_atom  := [] ;
|}.

Definition Scontinue_split := {|
  pre          := [] ;
  paths        := [] ;
  normal_post  := [] ;
  continue_post:= [] ;
  break_post   := [] ;
  return_post  := [] ;
  normal_atom  := [] ;
  continue_atom:= [ atom_normal_intro [] ] ;
  break_atom   := [] ;
  return_atom  := [] ;
|}.

Definition Sreturn_split retval := {|
  pre          := [] ;
  paths        := [] ;
  normal_post  := [] ;
  continue_post:= [] ;
  break_post   := [] ;
  return_post  := [] ;
  normal_atom  := [] ;
  continue_atom:= [] ;
  break_atom   := [] ;
  return_atom  := [ atom_return_intro [] retval ] ;
|}.

Notation "f @ a" := (@option_map _ _ f a) (at level 55, right associativity).

(* Notation " a [[ f ]] b " := (option_map2 f a b) (at level 75, right associativity). *)

Notation "a ++ b" := (option_app a b)
    (at level 60, right associativity).


    (* (A:Type) (a:A) (c: Clight.statement) (a_stm': A -> statement c),
    statement c


Fixpoint make_bind_pre (A : Type) (a: A) (c: Clight.statement) (a_stm': A -> statement c) : option (list partial_pre_statement) :=
       *)

Definition basic_result : Type := unit.

Inductive result : basic_result -> Type :=
| result_intro (x:basic_result) : result x
| result_binded (A:Type) (x: basic_result) (res' : A -> result x) : result x.

Inductive binded_results : list basic_result -> Type :=
| binded_results_nil : binded_results []
| binded_results_cons : 
    forall (x:basic_result) (x':result x) xs (xsb: binded_results xs),
      binded_results (x::xs).

Definition foo_fst {A:Type} x xs (res' : A -> binded_results (x::xs)) : A -> result x :=
  fun a => 
    match (res' a) with
    | binded_results_cons x x' xs xsb => x'
    end.


Definition foo_snd {A:Type} x xs (res' : A -> binded_results (x::xs)) : A -> binded_results xs :=
  fun a => 
    match (res' a) with
    | binded_results_cons x x' xs xsb => xsb
    end.

Fixpoint foo {A:Type} (res: list basic_result):
  (A -> binded_results res) -> binded_results res :=
  match res with
  | nil => fun res' => binded_results_nil
  | x::xs =>
     fun res' =>
      binded_results_cons 
        x (result_binded A x (foo_fst x xs res'))
        xs (foo xs (foo_snd x xs res'))
  end.


Fixpoint split_normal_atom c_stm ss (stm: statement c_stm ss) : option (list atom_normal_statement) :=
  match ss with
  | SSsequence s1 s2 


    match stm with
    | Ssequence s1 s2 ss1 ss2 c1 c2 =>
        atoms_conn_atoms (split_normal_atom c1 ss1) (split_normal_atom c2 ss2)
    | Sassert a =>
        Some []
    | Sskip =>
        Some [ nil ]
    | Sgiven A a c ss stm':

      statement c ss.




    | Sassert a => Some []
    (* | Sexgiven A a ass c => *)
        
    | Sgiven A a c a_stm' =>
        split_normal_atom c (a_stm' a)
    | Ssequence c1 c2 s1 s2 =>
        split_normal_atom c1 s1 ++ split_normal_atom c2 s2
    | _ => None
    end.


Fixpoint split_normal_atom c_stm (stm: statement c_stm) : option (list atom_normal_statement) :=
    match c_stm with
    | Clight.Ssequence s1 s2 =>
        split_normal_atom c1 s1 ++ split_normal_atom c2 s2
    | _ => None
    end.

Fixpoint split_normal_atom c_stm (stm: statement c_stm) : option (list atom_normal_statement) :=
  match stm with
  | Sassert a              => Some []
  | Sexgiven A a' c_stm    => Some [] 
  | Sgiven A a c_stm stm'  => 
      (* let res' := split_normal_atom c_stm (stm' a) *)
None

  | Sassign e1 e2         => Some [ atom_normal_intro [ inr (ASassign e1 e2) ] ]
  | Sset i e              => Some [ atom_normal_intro [ inr (ASset i e) ] ]
  | Sskip                 => Some [ atom_normal_intro [] ]
  | Sbreak                => Some []
  | Scontinue             => Some []
  | Sreturn rv            => Some []
  | Ssequence s1 s2       => 
      atoms_conn_atoms (split_normal_atom s1) (split_normal_atom s2)
  | Sifthenelse e s1 s2   =>
  (add_bexp_to_normal_atoms e) @ (split_normal_atom s1) 
  ++ (add_bexp_to_normal_atoms (Cnot e)) @ (split_normal_atom s2)

  | Sloop LINull s1 s2       =>
  split_break_atom s1 ++ atoms_conn_atoms (split_normal_atom s1) (split_break_atom s2) 
  ++ atoms_conn_atoms (split_continue_atom s1) (split_break_atom s2)
  ++ atoms_conn_atoms (split_normal_atom s2) (split_break_atom s1)
  | Sloop (LISingle inv) s1 s2       => Some []
  | Sloop (LIDouble inv1 inv2) s1 s2       => Some []
  
  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end

with split_continue_atom c_stm (stm: statement c_stm)  : option (list atom_normal_statement) :=
  match stm with
  | Sassert a             => Some []
  | Stopgiven A a stm'    => Some [] 
  | Sgiven A a ass' stm'  => Some []
  | Sassign e1 e2         => Some []
  | Sset i e              => Some []
  | Sskip                 => Some []
  | Sbreak                => Some []
  | Scontinue             => Some [ atom_normal_intro [] ]
  | Sreturn rv            => Some []
  | Ssequence s1 s2       =>
  split_continue_atom s1 ++ atoms_conn_atoms (split_normal_atom s1) (split_continue_atom s2)

  | Sifthenelse e s1 s2   =>
  (add_bexp_to_normal_atoms e) @ (split_continue_atom s1) 
  ++ (add_bexp_to_normal_atoms (Cnot e)) @ (split_continue_atom s2)

  | Sloop LINull s1 s2       => Some []
  | Sloop (LISingle inv) s1 s2       => Some []
  | Sloop (LIDouble inv1 inv2) s1 s2       => Some []
  
  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end

with split_break_atom c_stm (stm: statement c_stm)  : option (list atom_normal_statement) :=
  match stm with
  | Sassert a             => Some [] 
  | Stopgiven A a stm'    => Some [] 
  | Sgiven A a ass' stm'  => Some []
  | Sassign e1 e2         => Some []
  | Sset i e              => Some []
  | Sskip                 => Some []
  | Sbreak                => Some [ atom_normal_intro [] ]
  | Scontinue             => Some []
  | Sreturn rv            => Some []
  | Ssequence s1 s2       =>
  split_break_atom s1 ++ atoms_conn_atoms (split_normal_atom s1) (split_break_atom s2) 

  | Sifthenelse e s1 s2   =>
  (add_bexp_to_normal_atoms e) @ (split_break_atom s1) 
  ++ (add_bexp_to_normal_atoms (Cnot e)) @ (split_break_atom s2)

  | Sloop LINull s1 s2       => Some []
  | Sloop (LISingle inv) s1 s2       => Some []
  | Sloop (LIDouble inv1 inv2) s1 s2       => Some []
  
  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end.

Fixpoint split_return_atom (stm: Split.statement) : option (list atom_return_statement) :=
  match stm with
  | Sassert a             => Some [] 
  | Stopgiven A a stm'    => Some [] 
  | Sgiven A a ass' stm'  => Some []
  | Sassign e1 e2         => Some []
  | Sset i e              => Some []
  | Sskip                 => Some []
  | Sbreak                => Some []
  | Scontinue             => Some []
  | Sreturn rv            => Some [ atom_return_intro [] rv ]
  | Ssequence s1 s2       =>
  split_return_atom s1 ++ atoms_conn_returns (split_normal_atom s1) (split_return_atom s2)

  | Sifthenelse e s1 s2   =>
  (add_bexp_to_return_atoms e) @ (split_return_atom s1) 
  ++ (add_bexp_to_return_atoms (Cnot e)) @ (split_return_atom s2)

  | Sloop LINull s1 s2       =>
  split_return_atom s1 ++ atoms_conn_returns (split_normal_atom s1) (split_return_atom s2) 
  ++ atoms_conn_returns (split_continue_atom s1) (split_return_atom s2)
  ++ atoms_conn_returns (split_normal_atom s2) (split_return_atom s1)
  | Sloop (LISingle inv) s1 s2       => Some []
  | Sloop (LIDouble inv1 inv2) s1 s2       => Some []

  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end
.

Check sigT.
Print sigT.

Search sigT.

Print sig.

Fixpoint split_pre (stm: Split.statement) : option (sigT (list partial_pre_statement)) := 
  match stm with
  | Sassert a             => Some [ partial_pre_intro [] a ] 
  | Stopgiven A a stm'    => Some [ ]
  | Sgiven A a ass' stm'  => Some [ partial_pre_intro [] (EX x, ass' x)]
  | Sassign e1 e2         => Some []
  | Sset i e              => Some []
  | Sskip                 => Some []
  | Sbreak                => Some []
  | Scontinue             => Some []
  | Sreturn rv            => Some []
  | Ssequence s1 s2       =>
      split_pre s1 ++
      (atoms_conn_pres (split_normal_atom s1) (split_pre s2))
  | Sifthenelse e s1 s2   =>
      (add_bexp_to_partial_pres e) @ (split_pre s1) ++ 
      (add_bexp_to_partial_pres (Cnot e)) @ (split_pre s2)
  | Sloop LINull s1 s2       =>
      (split_pre s1) ++ 
      atoms_conn_pres (split_normal_atom s1) (split_pre s2) ++ 
      atoms_conn_pres (split_continue_atom s1) (split_pre s2)
  | Sloop (LISingle inv) s1 s2       =>
      Some [ partial_pre_intro [] inv ]
  | Sloop (LIDouble inv1 inv2) s1 s2       =>
      Some [ partial_pre_intro [] inv1 ]
  
  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end
.

Fixpoint split_normal_post (stm: Split.statement) : option (list partial_post_statement) :=
  match stm with
  | Sassert a             => Some [ partial_post_intro a [] ]
  | Stopgiven A a stm'    => Some [] 
  | Sgiven A a ass' stm'  => Some []
  | Sassign e1 e2         => Some []
  | Sset i e              => Some []
  | Sskip                 => Some []
  | Sbreak                => Some []
  | Scontinue             => Some []
  | Sreturn rv            => Some []
  | Ssequence s1 s2       =>
      split_normal_post s2 ++
      posts_conn_atoms (split_normal_post s1) (split_normal_atom s2)
  | Sifthenelse e s1 s2   =>
  split_normal_post s1 ++ split_normal_post s2

  | Sloop LINull s1 s2       =>
  (split_break_post s1) ++ (split_break_post s2) 
  ++ (posts_conn_atoms (split_normal_post s1) (split_break_atom s2)) 
  ++ (posts_conn_atoms (split_normal_post s2) (split_break_atom s1))
  ++ (posts_conn_atoms (split_continue_post s1) (split_break_atom s2)) 
  ++ (posts_conn_atoms (split_normal_post s2) (atoms_conn_atoms (split_normal_atom s1) (split_break_atom s2)))
  ++ (posts_conn_atoms (split_normal_post s2) (atoms_conn_atoms (split_continue_atom s1) (split_break_atom s2)))
  ++ (posts_conn_atoms (split_normal_post s1) (atoms_conn_atoms (split_normal_atom s2) (split_break_atom s1)))
  ++ (posts_conn_atoms (split_continue_post s1) (atoms_conn_atoms (split_normal_atom s2) (split_break_atom s1)))
  | Sloop (LISingle inv) s1 s2       =>
  split_break_post s1 ++ split_break_post s2 ++
  (add_P_to_normal_atoms inv) @ (split_break_atom s1) ++
  (add_P_to_normal_atoms inv) @ (atoms_conn_atoms (split_normal_atom s1) (split_break_atom s2)) ++
  (add_P_to_normal_atoms inv) @ (atoms_conn_atoms (split_continue_atom s1) (split_break_atom s2)) ++
  posts_conn_atoms (split_normal_post s1) (split_break_atom s2) ++
  posts_conn_atoms (split_continue_post s1) (split_break_atom s2)
  | Sloop (LIDouble inv1 inv2) s1 s2       =>
  split_break_post s1 ++ split_break_post s2 ++
  (add_P_to_normal_atoms inv1)@ (split_break_atom s1) ++
  (add_P_to_normal_atoms inv2)@ (split_break_atom s2)
  
  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end

with split_continue_post (stm: Split.statement) : option (list partial_post_statement) :=
  match stm with
  | Sassert a             => Some []
  | Stopgiven A a stm'    => Some [] 
  | Sgiven A a ass' stm'  => Some []
  | Sassign e1 e2         => Some []
  | Sset i e              => Some []
  | Sskip                 => Some []
  | Sbreak                => Some []
  | Scontinue             => Some []
  | Sreturn rv            => Some []
  | Ssequence s1 s2       =>
      split_continue_post s1 ++ split_continue_post s2
      ++ posts_conn_atoms (split_normal_post s1) (split_continue_atom s2)
  | Sifthenelse e s1 s2   =>
  split_continue_post s1 ++ split_continue_post s2

  | Sloop LINull s1 s2       => Some []
  | Sloop (LISingle inv) s1 s2       => Some []
  | Sloop (LIDouble inv1 inv2) s1 s2       => Some []
  
  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end

with split_break_post (stm: Split.statement) : option (list partial_post_statement) :=
  match stm with
  | Sassert a             => Some []
  | Stopgiven A a stm'    => Some [] 
  | Sgiven A a ass' stm'  => Some []
  | Sassign e1 e2         => Some []
  | Sset i e              => Some []
  | Sskip                 => Some []
  | Sbreak                => Some []
  | Scontinue             => Some []
  | Sreturn rv            => Some []
  | Ssequence s1 s2       =>
      split_break_post s1 ++ split_break_post s2
      ++ posts_conn_atoms (split_normal_post s1) (split_break_atom s2)
  | Sifthenelse e s1 s2   =>
  split_break_post s1 ++ split_break_post s2

  | Sloop LINull s1 s2       => Some []
  | Sloop (LISingle inv) s1 s2       => Some []
  | Sloop (LIDouble inv1 inv2) s1 s2       => Some []
  
  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end
.

Fixpoint split_return_post (stm: Split.statement) : option (list partial_return_statement) :=
  match stm with
  | Sassert a             => Some []
  | Stopgiven A a stm'    => Some [] 
  | Sgiven A a ass' stm'  => Some []
  | Sassign e1 e2         => Some []
  | Sset i e              => Some []
  | Sskip                 => Some []
  | Sbreak                => Some []
  | Scontinue             => Some []
  | Sreturn rv            => Some []
  | Ssequence s1 s2       =>
      split_return_post s1 ++ split_return_post s2
      ++ posts_conn_returns (split_normal_post s1) (split_return_atom s2)
  | Sifthenelse e s1 s2   =>
  split_return_post s1 ++ split_return_post s2

  | Sloop LINull s1 s2       =>
      (split_return_post s1) ++ (split_return_post s2)
      ++ posts_conn_returns(split_normal_post s1)(split_return_atom s2) 
      ++ posts_conn_returns(split_continue_post s1)(split_return_atom s2)
      ++ posts_conn_returns(split_normal_post s2)(split_return_atom s1)
      ++ (posts_conn_returns (split_normal_post s2) (atoms_conn_returns (split_normal_atom s1) (split_return_atom s2)))
      ++ (posts_conn_returns (split_normal_post s2) (atoms_conn_returns (split_continue_atom s1) (split_return_atom s2)))
      ++ (posts_conn_returns (split_normal_post s1) (atoms_conn_returns (split_normal_atom s2) (split_return_atom s1)))
      ++ (posts_conn_returns (split_continue_post s1) (atoms_conn_returns (split_normal_atom s2) (split_return_atom s1)))
  | Sloop (LISingle inv) s1 s2       =>
  (split_return_post s1) ++ (split_return_post s2) ++
  (add_P_to_return_atoms inv) @ (split_return_atom s1) ++
  (add_P_to_return_atoms inv) @ (atoms_conn_returns (split_normal_atom s1) (split_return_atom s2)) ++
  (add_P_to_return_atoms inv) @ (atoms_conn_returns (split_continue_atom s1) (split_return_atom s2)) ++
  posts_conn_returns (split_normal_post s1) (split_return_atom s2) ++
  posts_conn_returns (split_continue_post s1) (split_return_atom s2)
  | Sloop (LIDouble inv1 inv2) s1 s2       =>
  (split_return_post s1) ++ (split_return_post s2) ++
  (add_P_to_return_atoms inv1) @ (split_return_atom s1) ++
  (add_P_to_return_atoms inv2) @ (split_return_atom s2) 
  
  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end
.

Definition isnil {A : Type} (l : list A) := 
  match l with
  | [] => true
  | _ :: _ => false
  end.

Definition loop_cont_valid (s2: Split.statement) : bool :=
  match (split_continue_atom s2), (split_continue_post s2) with
  | Some nil, Some nil => true
  | _, _ => false
  end
.

Definition loop_has_assert (s1 s2: Split.statement):= 
  match (split_pre s1), (split_pre s2) with
  | Some (_ :: _), Some (_ :: _) => true
  | _, _ => false
  end
.

Definition no_unannote_loop1 (s1 s2: Split.statement):= 
  match (split_normal_atom s1), (split_normal_atom s2) with
  | Some (_ :: _), _ => true
  | _, Some (_ :: _) => true
  | _, _ => false
  end
.

Definition no_unannote_loop2 (s1 s2: Split.statement):= 
  match (split_continue_atom s1), (split_normal_atom s2) with
  | Some (_ :: _), _ => true
  | _, Some (_ :: _) => true
  | _, _ => false
  end
.


Definition is_0inv_valid (s1 s2: Split.statement) : bool :=
  loop_cont_valid s2 && loop_has_assert s1 s2 && no_unannote_loop1 s1 s2 && no_unannote_loop2 s1 s2 
.


Fixpoint split_path (stm: Split.statement) : option (list path_statement) :=
  match stm with
  | Sassert a             => Some []
  | Stopgiven A a stm'    => Some [] 
  | Sgiven A a ass' stm'  => Some []
  | Sassign e1 e2         => Some []
  | Sset i e              => Some []
  | Sskip                 => Some []
  | Sbreak                => Some []
  | Scontinue             => Some []
  | Sreturn rv            => Some []
  | Ssequence s1 s2       =>
      split_path s1 ++ 
      split_path s2 ++ 
      posts_conn_pres (split_normal_post s1) (split_pre s2)
  | Sifthenelse e s1 s2   =>
      split_path s1 ++ split_path s2
  | Sloop LINull s1 s2       =>
      if is_0inv_valid s1 s2 then
        split_path s1 ++ 
        split_path s2 ++ 
        posts_conn_pres (split_normal_post s1) (split_pre s2) ++
        posts_conn_pres (split_continue_post s1) (split_pre s2)++
        posts_conn_pres (split_normal_post s2) ((split_pre s1)) ++
        (posts_conn_pres (posts_conn_atoms (split_normal_post s1) (split_normal_atom s2)) ((split_pre s1))) ++
        (posts_conn_pres (posts_conn_atoms (split_continue_post s1) (split_normal_atom s2)) ((split_pre s1))) ++
        (posts_conn_pres (posts_conn_atoms (split_normal_post s2) (split_normal_atom s1)) (split_pre s2)) ++
        (posts_conn_pres (posts_conn_atoms (split_normal_post s2) (split_continue_atom s1)) (split_pre s2))
      else None
  | Sloop (LISingle inv) s1 s2       =>
     if loop_cont_valid s2 then
      (add_P_to_partial_pres inv) @ ((split_pre s1)) ++
      (add_P_to_partial_pres inv) @ (atoms_conn_pres (split_normal_atom s1) (split_pre s2)) ++
      (add_P_to_partial_pres inv) @ (atoms_conn_pres 
          (split_normal_atom s1) ((fun a => add_Q_to_normal_atoms a inv) @ (split_normal_atom s2))) ++
      (add_P_to_partial_pres inv) @ (atoms_conn_pres 
          (split_continue_atom s1) ((fun a => add_Q_to_normal_atoms a inv) @ (split_normal_atom s2))) ++
      (add_P_to_partial_pres inv) @ (atoms_conn_pres (split_continue_atom s1) (split_pre s2)) ++
      split_path s1 ++ split_path s2 ++
      posts_conn_pres (split_normal_post s1) (split_pre s2) ++
      posts_conn_pres (split_normal_post s1) ((fun a => add_Q_to_normal_atoms a inv) @ (split_normal_atom s2)) ++
      posts_conn_pres (split_continue_post s1) (split_pre s2) ++
      posts_conn_pres (split_continue_post s1) ((fun a => add_Q_to_normal_atoms a inv) @ (split_normal_atom s2)) ++
      (fun a => add_Q_to_normal_posts a inv) @ (split_normal_post s2)
    else None
  | Sloop (LIDouble inv1 inv2) s1 s2       =>
     if loop_cont_valid s2 then
      (add_P_to_partial_pres inv1) @ (split_pre s1) ++
      (add_P_to_partial_pres inv1) @ ((fun a => add_Q_to_normal_atoms a inv2) @ (split_normal_atom s1)) ++
      (add_P_to_partial_pres inv1) @ ((fun a => add_Q_to_normal_atoms a inv2) @ (split_continue_atom s1)) ++
      (fun a => add_Q_to_normal_posts a inv2) @ (split_normal_post s1) ++
      (fun a => add_Q_to_normal_posts a inv2) @ (split_continue_post s1)  ++
      (add_P_to_partial_pres inv2) @ (split_pre s2) ++
      (add_P_to_partial_pres inv2) @ ((fun a => add_Q_to_normal_atoms a inv1) @ (split_normal_atom s2)) ++
      (fun a => add_Q_to_normal_posts a inv1) @ (split_normal_post s2) ++
      (fun a => add_Q_to_normal_posts a inv1) @ (split_continue_post s2) ++
      split_path s1 ++ split_path s2
     else None

  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end.


Definition split_result (stm: Split.statement) : option split_result_basic :=
  match split_pre stm, split_path stm, 
        split_normal_post stm,
        split_continue_post stm,
        split_break_post stm,
        split_return_post stm,
        split_normal_atom stm,
        split_continue_atom stm,
        split_break_atom stm,
        split_return_atom stm with
  | Some pre, Some paths, Some normal_post, Some continue_post, 
    Some break_post, Some return_post, Some normal_atom, 
    Some continue_atom, Some break_atom, Some return_atom => 
    Some {|
      pre := pre;
      paths := paths;
      normal_post := normal_post;
      continue_post := continue_post;
      break_post := break_post;
      return_post := return_post;
      normal_atom := normal_atom;
      continue_atom := continue_atom;
      break_atom := break_atom;
      return_atom := return_atom
    |}
  | _, _, _, _, _, _, _, _, _, _ => None
  end.




Definition FALSE := (PROP (False) LOCAL () SEP ()).

Fixpoint to_Clight  (a: atom_statement) : Clight.statement :=
match a with
| ASskip => Clight.Sskip
| ASassign e1 e2 => Clight.Sassign e1 e2
| ASset id e => Clight.Sset id e
| AScall id e elis => Clight.Scall id e elis
end.

End Split.