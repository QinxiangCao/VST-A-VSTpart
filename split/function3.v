Require Import AClight.AClight.
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


Notation "( x ; y )" := (existT _ x y) (at level 0, format "( x ; '/ ' y )").
Notation "x .1" := (projT1 x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (projT2 x) (at level 1, left associativity, format "x .2").

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

Inductive binded_of {R : Type} (r:R) : Type :=
| binded_basic:  binded_of r
| binded_intro (A: Type) (HA: inhabited A) : 
   (A -> binded_of r) -> binded_of r.


(* TODO: is this correct? *)
Inductive list_binded_of {R : Type} : list R -> Type :=
| list_binded_nil : list_binded_of []
| list_binded_cons (r:R) (r': binded_of r) (l: list R)
                   (l':list_binded_of l) : list_binded_of (r::l).

(* Check list_binded_nil.
Parameter a : Type.
Parameter a' : binded_of a.
Parameter b : Type.
Parameter b' : binded_of b.
Check (list_binded_cons a a' [b] (list_binded_cons b b' [] list_binded_nil)). *)


Definition binded_hd {R:Type} (x: R) (xs: list R) 
  (res' : list_binded_of (x::xs)) : binded_of x :=
    match res' with
    | list_binded_cons x x' xs xsb => x'
    end.


Definition binded_tl {R:Type} (x: R) (xs: list R)
  (res' : list_binded_of (x::xs)) : list_binded_of xs :=
    match (res') with
    | list_binded_cons x x' xs xsb => xsb
    end.

Fixpoint app_bind_aux {A:Type}
  (l:list A) 
  (m:list A) :
  (list_binded_of l) ->
  (list_binded_of m) ->
  {n : list A & list_binded_of n} :=
match l with
| [] => fun l' m' => (m; m')
| a :: l1 =>
    fun (l': list_binded_of (a::l1)) m' =>
    let a' := binded_hd a l1 l' in
    let l1' := binded_tl a l1 l' in
    match app_bind_aux l1 m l1' m' with
    | (n; n') => (a :: n; list_binded_cons a a' n n')
    end
end.


Definition app_bind  {A:Type} 
  (l:  { l : list A & list_binded_of l }) 
  (m:  { m : list A & list_binded_of m }) :
  { n : list A & list_binded_of n } :=
app_bind_aux l.1 m.1 l.2 m.2.

(* Fixpoint concat_bind {A:Type} (xss: list { xs : list A & list_binded_of xs }) : { ys : list A & list_binded_of ys } :=
match xss with
| nil =>  ( [] ; list_binded_nil)
| ( xs ; xsb ) :: xss' =>
  match concat_bind xss' with
  | ( xs' ; xsb' ) => 
    ( xs ++ xs' ; app_bind (xs ; xsb) (xs' ; xsb'))
  end
end.
| ( [] ; list_binded_nil ) =>
| ( xs :: xss' ;
     ) *)

(* normal + binded product *)
(* Fixpoint product_map_nb {A B C: Type} (f: A -> B -> C) 
  (xs: { xs : list A | list_binded_of xs })
  (ys: { ys : list B | list_binded_of ys }) : 
  {zs: list C | list_binded_of C } :=
  concat (map (fun x => map (f x) ys) xs). *)



Inductive path_statement : Type :=
| path_intro (pre:assert) (path:path) (post:assert)
| binded_path (A:Type) (HA:inhabited A) (path': A -> path_statement) : path_statement.

Notation path_statement_binded := (binded_of path_statement).
Notation path_statements := (list path_statement).
Notation path_statements_binded := (list_binded_of path_statement).


Inductive partial_pre_statement : Type :=
| partial_pre_intro (path:path) (post:assert)
.

Notation partial_pre_statement_binded := (binded_of partial_pre_statement).
Notation partial_pre_statements := (list partial_pre_statement).
Notation partial_pre_statements_binded := (list_binded_of partial_pre_statement).


Inductive partial_post_statement : Type :=
| partial_post_intro (pre:assert) (path:path)
.

Notation partial_post_statement_binded := (binded_of partial_post_statement).
Notation partial_post_statements := (list partial_post_statement).
Notation partial_post_statements_binded := (list_binded_of partial_post_statement).

Inductive partial_return_statement : Type :=
| partial_return_intro (pre:assert) (path:path) (retval: option expr)
.

Notation partial_return_statement_binded := (binded_of partial_post_statement).
Notation partial_return_statements := (list partial_return_statement).
Notation partial_return_statements_binded := (list_binded_of partial_return_statement).

Inductive atom_normal_statement: Type :=
| atom_normal_intro (path: path).

Notation atom_normal_statements := (list atom_normal_statement).

Inductive atom_return_statement: Type :=
| atom_return_intro (path: path) (retval: option expr).  

Notation atom_return_statements := (list atom_return_statement).

Record split_result_basic: Type := Bres_Pack {
  pre   : list partial_pre_statement;
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



Inductive simple_stmt : Type.

Inductive simple_result : Type.
(* split results erased by binders and assertion contents *)

Fixpoint split_basic (s:simple_stmt) : simple_result.
Admitted.

Inductive statement : simple_stmt -> Type :=
| foo (s:simple_stmt) : statement s .
(* statements that produce shapes like simple_result *)

Inductive result : simple_result -> Type :=
| foo' (s:simple_result) : result s .
(* simple_result enriched with binders and assertions *)

(* Fixpoint flatten_given {A:Type} (res: simple_result) :
	(A -> split_result res) -> split_result res. *)

Definition combine_sequence_basic : simple_result -> simple_result -> simple_result.
Admitted.

(* Definition combine_sequence 
     res1 res2 s1 s2 res
    (H: res = combine_sequence_basic res1 res2)
		(split_result res1) (split_result res2)
   : split_result res. *)
(* How to implement? *)

Fixpoint split_hint 
  (cstm: simple_stmt)
  (Astm: statement cstm) : result (split_basic cstm) :=
match Astm with
| Sgiven A stm' =>
		flatten_given res (fun a => split_hint res (stm' a))
| Ssequence s1 s2 c1 c2  =>
		combine_sequence (split_hint c1 s1 : split_result (split_basic c1)) 
										 (split_hint c2 s2 : split_result (split_basic c2))
      : split_result (split_basic (c1;;c2))






(* Inductive result : basic_result -> Type :=
| result_intro (x:basic_result) : result x
| result_binded (A:Type) (x: basic_result) (res' : A -> result x) : result x.

Inductive binded_results : list basic_result -> Type :=
| binded_results_nil : binded_results []
| binded_results_cons : 
    forall (x:basic_result) (x':result x) xs (xsb: binded_results xs),
      binded_results (x::xs). *)



Definition hd_of {R A:Type} (x: R) (xs: list R) 
  (res' : A -> list_binded_of (x::xs)) : A -> binded_of x :=
  fun a => 
    match (res' a) with
    | list_binded_cons x x' xs xsb => x'
    end.


Definition tl_of {R A:Type} (x: R) (xs: list R)
  (res' : A -> list_binded_of (x::xs)) : A -> list_binded_of xs :=
  fun a => 
    match (res' a) with
    | list_binded_cons x x' xs xsb => xsb
    end.

Fixpoint flatten_given' {R A:Type} (res: list R) (HA: inhabited A):
(A -> list_binded_of res) -> list_binded_of res :=
match res with
| nil => fun res' => (list_binded_nil)
| x::xs =>
    fun res' =>
    list_binded_cons
      x (binded_intro x A HA (hd_of x xs res'))
      xs (flatten_given' xs HA (tl_of x xs res'))
end.

(* Fixpoint binded_map {R1 R2: Type} 
  (f_basic: R1 -> R2)
  (f: forall (r1:R1), binded_of r1 -> binded_of (f_basic r1)) 
  (res_basic: list R1)
  (res: list_binded_of res_basic) : list_binded_of (map f_basic res_basic) :=
match res with
| list_binded_nil => list_binded_nil
| list_binded_cons x x' xs xs' =>
  list_binded_cons x (f x x') xs (binded_map f xs xs')
end. *)

(*****************************)
(*****************************)
(* Basic Operations on paths *)
(*****************************)
(*****************************)
Fixpoint add_P_to_partial_pre P path Q (pre: binded_of (partial_pre_intro path Q)) : path_statement :=
  match pre with
  | binded_basic =>
      (path_intro P path Q)
  | binded_intro A HA pre' =>
      binded_path A HA (fun x => add_P_to_partial_pre P path Q (pre' x))
  end.

(* Fixpoint add_P_to_partial_pres_basic P pres_basic :=
  match pres_basic with
  | [] => []
  | (partial_pre_intro path Q)::xs => 
        (path_intro P path Q) :: add_P_to_partial_pres_basic P xs
  end. *)

Fixpoint add_P_to_partial_pres P pres_basic (pres:list_binded_of pres_basic) : list path_statement:=
  match pres with
  | list_binded_nil => []
  | list_binded_cons (partial_pre_intro path Q) x' xs xs' =>
      (add_P_to_partial_pre P path Q x') :: add_P_to_partial_pres P xs xs'
  end.

  (* match pres_basic with
  | [] => fun pres => list_binded_nil
  | (partial_pre_intro path Q)::xs =>
      fun pres => match pres with
      | list_binded_cons (partial_pre_intro path Q) x'
                          xs pres' =>
       list_binded_cons 
        (path_intro P path Q)
        (add_P_to_partial_pre P path Q x')
        (add_P_to_partial_pres_basic P xs)
        (add_P_to_partial_pres P xs pres')
      end
  end. *)

Definition add_P_to_normal_atom_basic P atom := match atom with
  | atom_normal_intro path => partial_post_intro P path end.

(* how to define the function when the output type is a dependent type ? *)


Fixpoint add_P_to_normal_atoms
  (P: assert) 
  (atoms: list atom_normal_statement)
  :  { posts : partial_post_statements & list_binded_of posts } :=
  match atoms with
  | [] => existT _ nil (list_binded_nil)
  | (atom_normal_intro path)::atoms' =>
    match add_P_to_normal_atoms P atoms' with
    | existT posts_basic' posts' =>
      existT _
      ((partial_post_intro P path):: posts_basic')
      (list_binded_cons 
          (partial_post_intro P path)
          (binded_basic (partial_post_intro P path))
          posts_basic'
          posts')
    end
  end.

(* Definition add_P_to_normal_atom_basic P atom := match atom with
| atom_normal_intro path => partial_post_intro P path end.

Definition add_P_to_normal_atom P atom := 
  (binded_basic (add_P_to_normal_atom_basic P atom)).

Definition add_P_to_normal_atoms P := map (add_P_to_normal_atom P). *)

(* Definition add_P_to_return_atom P atom := match atom with
| atom_return_intro path retval => partial_return_intro P path retval end.

Definition add_P_to_return_atoms P := map (add_P_to_return_atom P). *)


Fixpoint add_P_to_return_atoms
  (P: assert) 
  (atoms: list atom_return_statement)
  :  { posts : partial_return_statements & list_binded_of posts } :=
  match atoms with
  | [] => existT _ nil (list_binded_nil)
  | (atom_return_intro path ret)::atoms' =>
    match add_P_to_return_atoms P atoms' with
    | existT posts_basic' posts' =>
      existT (fun posts => list_binded_of posts)
      ((partial_return_intro P path ret):: posts_basic')
      (list_binded_cons 
          (partial_return_intro P path ret)
          (binded_basic (partial_return_intro P path ret))
          posts_basic'
          posts')
    end
  end.

Fixpoint add_Q_to_normal_post P path Q (post: binded_of (partial_post_intro P path)) : path_statement :=
  match post with
  | binded_basic  =>
      (path_intro P path Q)
  | binded_intro A HA post' =>
      binded_path A HA (fun x => add_Q_to_normal_post P path Q (post' x))
  end.

(* Fixpoint add_P_to_partial_pres_basic P pres_basic :=
  match pres_basic with
  | [] => []
  | (partial_pre_intro path Q)::xs => 
        (path_intro P path Q) :: add_P_to_partial_pres_basic P xs
  end. *)

Fixpoint add_Q_to_normal_posts Q posts_basic (pres:list_binded_of posts_basic) : list path_statement:=
  match pres with
  | list_binded_nil => []
  | list_binded_cons 
      (partial_post_intro P path) x' xs xs' =>
      (add_Q_to_normal_post P path Q x') :: add_Q_to_normal_posts P xs xs'
  end.

(* Fixpoint add_Q_to_normal_post Q post := match post with
| partial_post_intro P path => path_intro P path Q
| partial_post_binded A HA post' =>
    path_binded A HA (fun x => add_Q_to_normal_post Q (post' x))
end.

Definition add_Q_to_normal_posts posts Q := map (add_Q_to_normal_post Q) posts. *)

Fixpoint add_Q_to_normal_atoms
  (Q: assert) 
  (atoms: list atom_normal_statement)
  :  { pres : partial_pre_statements & list_binded_of pres } :=
  match atoms with
  | [] => existT _ nil (list_binded_nil)
  | (atom_normal_intro path)::atoms' =>
    match add_Q_to_normal_atoms Q atoms' with
    | existT pres_basic' pres' =>
      existT _
      ((partial_pre_intro path Q):: pres_basic')
      (list_binded_cons 
          (partial_pre_intro path Q)
          (binded_basic (partial_pre_intro path Q))
          pres_basic'
          pres')
    end
  end.

(* Definition add_Q_to_normal_atom Q atom := match atom with
| atom_normal_intro path => partial_pre_intro path Q end.

Definition add_Q_to_normal_atoms atoms Q := map (add_Q_to_normal_atom Q) atoms. *)

Fixpoint add_bexp_to_partial_pre (bexp: expr) path Q
  (pre: binded_of (partial_pre_intro path Q))
  : binded_of (partial_pre_intro (inl bexp :: path) Q) :=
match pre with
| binded_basic => 
    binded_basic (partial_pre_intro (inl bexp :: path) Q)
| binded_intro A HA pre' =>
    binded_intro (partial_pre_intro (inl bexp :: path) Q) A HA
      (fun a => add_bexp_to_partial_pre bexp path Q (pre' a))
end.


Fixpoint add_bexp_to_partial_pres bexp
  pres_basic :
  list_binded_of pres_basic ->
  { pres : partial_pre_statements & list_binded_of pres } :=
match pres_basic with
| [] => fun _ => existT _ nil (list_binded_nil)
| (partial_pre_intro path Q) :: pres_basic' =>
  fun pres => 
  let pres_hd := binded_hd (partial_pre_intro path Q) pres_basic' pres in
  let pres_tl := binded_tl (partial_pre_intro path Q) pres_basic' pres in
    match add_bexp_to_partial_pres bexp pres_basic' pres_tl with
    | existT pre_basic'' pre'' =>
      existT _ ((partial_pre_intro (inl bexp :: path) Q) :: pre_basic'')
        (list_binded_cons
          (partial_pre_intro (inl bexp :: path) Q)
          (add_bexp_to_partial_pre bexp path Q pres_hd)
          pre_basic'' pre'')
    end
end.



(* Fixpoint add_bexp_to_partial_pre bexp pre := match pre with
| partial_pre_intro path Q => partial_pre_intro ((inl bexp)::path) Q
| partial_pre_binded A HA pre' =>
    partial_pre_binded A HA 
      (fun x => add_bexp_to_partial_pre bexp (pre' x))
end.

Definition add_bexp_to_partial_pres bexp := map (add_bexp_to_partial_pre bexp). *)

Definition add_bexp_to_normal_atom bexp atom := match atom with
| atom_normal_intro path => atom_normal_intro ((inl bexp)::path) end.

Definition add_bexp_to_normal_atoms bexp := map (add_bexp_to_normal_atom bexp).

Definition add_bexp_to_return_atom bexp atom := match atom with
| atom_return_intro path retval => atom_return_intro ((inl bexp)::path) retval end.

Definition add_bexp_to_return_atoms bexp := map (add_bexp_to_return_atom bexp).

Fixpoint atom_conn_pre_aux p1 p2 Q (pre: binded_of (partial_pre_intro p2 Q)) : binded_of (partial_pre_intro (p1 ++ p2) Q) :=
  match pre with
  | binded_basic => binded_basic (partial_pre_intro (p1 ++ p2) Q)
  | binded_intro A HA pre' =>
      binded_intro (partial_pre_intro (p1 ++ p2) Q) A HA
        (fun a => atom_conn_pre_aux p1 p2 Q (pre' a))
end.



Definition atom_conn_pre atom pre_basic : 
  binded_of pre_basic -> {res_pre: _ & binded_of res_pre }  := 
  match atom with atom_normal_intro p1 =>
    match pre_basic with
    partial_pre_intro p2 Q => 
      fun (pre: binded_of (partial_pre_intro p2 Q)) =>
        ( (partial_pre_intro (p1 ++ p2) Q);  atom_conn_pre_aux p1 p2 Q pre)
    end
  end.
(* 
Fixpoint atom_conn_pre atom pre : partial_pre_statement :=
  match atom with atom_normal_intro p1 =>
    match pre with 
    | partial_pre_intro p2 Q =>
        partial_pre_intro (p1 ++ p2) Q 
    | partial_pre_binded A HA pre' =>
        partial_pre_binded A HA (fun x => atom_conn_pre atom (pre' x))
    end
  end. *)

Definition atoms_conn_pres (atoms : atom_normal_statements)
  (pres: { pres_basic: partial_pre_statements & binded_of pres_basic })
  : { pres_basic: partial_pre_statements & binded_of pres_basic }.
Admitted.

Definition atom_conn_atom atom1 atom2 : atom_normal_statement :=
  match atom1 with atom_normal_intro p1 =>
    match atom2 with atom_normal_intro p2 =>
    atom_normal_intro (p1 ++ p2) end
  end.

Fixpoint product_map {A B C: Type} (f: A -> B -> C) (xs: list A) (ys: list B) : list C :=
    concat (map (fun x => map (f x) ys) xs).

Definition atoms_conn_atoms := option_map2 (product_map atom_conn_atom).

Definition atom_conn_return atom1 atom2 : atom_return_statement :=
  match atom1 with atom_normal_intro p1 =>
    match atom2 with atom_return_intro p2 rv =>
    atom_return_intro (p1 ++ p2) rv end
  end.

Definition atoms_conn_returns := option_map2 (product_map atom_conn_return).

(* Fixpoint post_conn_atom post atom : partial_post_statement :=
  match post with 
  | partial_post_intro P p1 =>
    match atom with atom_normal_intro p2 =>
      partial_post_intro P (p1 ++ p2) end
  | partial_post_binded A HA post' =>
      partial_post_binded A HA 
        (fun x => post_conn_atom (post' x) atom )
  end.

Definition posts_conn_atoms := option_map2 (product_map post_conn_atom). *)

Definition posts_conn_atoms (atoms : atom_normal_statements)
  (posts: { posts_basic: partial_post_statements & binded_of posts_basic })
  : { posts_basic: partial_post_statements & binded_of posts_basic }.
Admitted.


(* Fixpoint post_conn_return post atom : partial_return_statement :=
  match post with
  | partial_post_intro P p1 =>
    match atom with atom_return_intro p2 rv =>
      partial_return_intro P (p1 ++ p2) rv end
  | partial_post_binded A HA post' =>
      partial_return_binded A HA 
        (fun x => post_conn_return (post' x) atom)
  end.

Definition posts_conn_returns := option_map2 (product_map post_conn_return). *)
  

Definition posts_conn_returns (atoms : atom_normal_statements)
  (posts: { posts_basic: partial_return_statements & binded_of posts_basic })
  : { posts_basic: partial_return_statements & binded_of posts_basic }.
Admitted.

(* Fixpoint post_conn_pre_aux P p1 pre : path_statement :=
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

Definition posts_conn_pres := option_map2 (product_map post_conn_pre). *)


Definition posts_conn_pres 
(pres: { pres_basic: partial_pre_statements & binded_of pres_basic })
(posts: { posts_basic: partial_return_statements & binded_of posts_basic })
: path_statements.
Admitted.


(*****************************)
(*****************************)
(* Combinations for language constructs *)
(*****************************)
(*****************************)

Inductive split_result : Type :=
| mk_split_result
    (path : path_statements)
    (normal_atom : atom_normal_statements)
    (break_atom  : atom_normal_statements)
    (continue_atom: atom_normal_statements)
    (return_atom: atom_return_statements)
    (pre_basic: partial_pre_statements)
    (pre: list_binded_of pre_basic)
    (normal_post_basic: partial_pre_statements)
    (normal_post: list_binded_of normal_post_basic)
    (break_post_basic: partial_post_statements)
    (break_post: list_binded_of break_post_basic)
    (continue_post_basic: partial_post_statements)
    (continue_post: list_binded_of continue_post_basic)
    (return_post_basic: partial_return_statements)
    (return_post: list_binded_of return_post_basic).


Fixpoint flatten_given {R A:Type} (res: list R) (HA: inhabited A):
(A -> list_binded_of res) -> list_binded_of res :=
match res with
| nil => fun res' => (list_binded_nil)
| x::xs =>
    fun res' =>
    list_binded_cons
      x (binded_intro x A HA (hd_of x xs res'))
      xs (flatten_given xs HA (tl_of x xs res'))
end.

(* Fixpoint flatten_given {R A:Type} (res: list R) (HA: inhabited A):
(A -> option { res : list R & list_binded_of res } ) ->
option (list_binded_of res) :=
match res with
| nil => fun res' => (list_binded_nil)
| x::xs =>
    fun res' =>
    list_binded_cons
      x (binded_intro x A HA (hd_of x xs res'))
      xs (flatten_given xs HA (tl_of x xs res'))
end. *)


Fixpoint split_normal_post_simple
  (cstm: Clight.statement) : partial_post_statements.

Admitted.

Fixpoint



Fixpoint split_normal_post (stm : AClight.statement) : 
  option { post: partial_post_statements & list_binded_of post } :=
  match stm with
  | Sgiven A stm' =>
      flatten_given
      match split_hint stm' with

  | _ => None
end.
(**********************************************)
(* combine a ex-given pre-condition to a split-result
   Ppre = EX a:A. P(a)
   P = P(a)
   res = res(a) *)
(**********************************************)
(* 
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
    (at level 60, right associativity). *)


    (* (A:Type) (a:A) (c: Clight.statement) (a_stm': A -> statement c),
    statement c


Fixpoint make_bind_pre (A : Type) (a: A) (c: Clight.statement) (a_stm': A -> statement c) : option (list partial_pre_statement) :=
       *)


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