(** TO Discuss:

Will the Binded-result style make the split-result non-modular to local changes?
- i.e. any change to ex-given clause will lead to a globally different split result

How to deal with sequence of given in loop invariants?
- the "new" parser should add some dummy assertions after loop invariants

e.g. 
Sloop
 INV = EX x y, ...
 c1 = ...
 c2 = ...

after parsing:
Sloop
 INV = EX x y, i(x,y)
 c1 = Sgiven x. EX y, i(x,y) ;
        Sgiven y. i(x,y); ...(loop body)
 c2 = ...


*)
Require Import AClight.AClight.
Require Import VST.floyd.proofauto.
Require Import Split.vst_ext.
Notation "x ;; y" := (Ssequence x y)  (at level 65) : logic.
Require Import VST.veric.semax_lemmas.

Axiom classic: forall P,  P \/ ~ P.

Module Split.

Inductive statement : Type :=
  | Sassert : assert -> statement
  | Stopgiven: forall (A: Type) (a:A),
    (**r Given a:A,
            ...statement(a)
    *)
       (A -> statement) -> statement
  | Sgiven: forall (A: Type) (a: A),
    (**r {{ EX a:A, ...assert(a) }}
         Given a:A,
            ...statement(a)
    *)
    (* requires a trivial inhaited witness to make [Split_to_Clight]
         recursive *)
    (* given-assert structure, which binds the
         quantified assertion and the Given cluase simultaneously *)
        (A -> assert) -> (A -> statement) -> statement
  | Sskip : statement                   (**r do nothing *)
  | Sassign : expr -> expr -> statement (**r assignment [lvalue = rvalue] *)
  | Sset : ident -> expr -> statement   (**r assignment [tempvar = rvalue] *)
  | Scall: option ident -> expr -> list expr -> statement (**r function call *)
  | Sbuiltin: option ident -> external_function -> typelist -> list expr -> statement (**r builtin invocation *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
  | Sloop: loop_invariant -> statement -> statement -> statement (**r infinite loop *)
  | Sbreak : statement                      (**r [break] statement *)
  | Scontinue : statement                   (**r [continue] statement *)
  | Sreturn : option expr -> statement      (**r [return] statement *)
  (* below are unimplemented commands *)
  | Slocal: assert -> nat -> statement -> assert -> statement
  | Sswitch : expr -> labeled_statements -> statement  (**r [switch] statement *)
  | Slabel : label -> statement -> statement
  | Sgoto : label -> statement

with labeled_statements : Type :=            (**r cases of a [switch] *)
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements.
                      (**r [None] is [default], [Some x] is [case x] *)


Fixpoint Split_to_Clight (stm: Split.statement) :=
  match stm with
  | Ssequence s1 s2 => Clight.Ssequence (Split_to_Clight s1) (Split_to_Clight s2)
  | Sifthenelse b s1 s2 => Clight.Sifthenelse b (Split_to_Clight s1) (Split_to_Clight s2)
  | Sloop _ s1 s2 => Clight.Sloop (Split_to_Clight s1) (Split_to_Clight s2)
  | Sswitch e sl => Clight.Sswitch e (Split_to_Clight_ls sl)
  | Sgiven A a ass stm => Split_to_Clight (stm a)
  | Sassign e1 e2 => Clight.Sassign e1 e2
  | Sset i e => Clight.Sset i e
  | Scall r e bl => Clight.Scall r e bl
  | Sbreak => Clight.Sbreak 
  | Scontinue => Clight.Scontinue 
  | Sreturn r => Clight.Sreturn r
  | _ => Clight.Sskip
  end
  with Split_to_Clight_ls sl :=
  match sl with LSnil => Clight.LSnil | LScons z s sl' => Clight.LScons z  (Split_to_Clight s)  (Split_to_Clight_ls sl')
  end.


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

Inductive split_result : Type :=
| split_result_error
| split_result_intro (res: split_result_basic).
(* The universally quantififed variables may be absent in some/most of the paths
i.e. binded_Vars = Union(given introduced variables) *)


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

Definition atoms_conn_pres := product_map atom_conn_pre.

Definition atom_conn_atom atom1 atom2 : atom_normal_statement :=
  match atom1 with atom_normal_intro p1 =>
    match atom2 with atom_normal_intro p2 =>
    atom_normal_intro (p1 ++ p2) end
  end.

Definition atoms_conn_atoms := product_map atom_conn_atom.

Definition atom_conn_return atom1 atom2 : atom_return_statement :=
  match atom1 with atom_normal_intro p1 =>
    match atom2 with atom_return_intro p2 rv =>
    atom_return_intro (p1 ++ p2) rv end
  end.

Definition atoms_conn_returns := product_map atom_conn_return.

Fixpoint post_conn_atom post atom : partial_post_statement :=
  match post with 
  | partial_post_intro P p1 =>
    match atom with atom_normal_intro p2 =>
      partial_post_intro P (p1 ++ p2) end
  | partial_post_binded A HA post' =>
      partial_post_binded A HA 
        (fun x => post_conn_atom (post' x) atom )
  end.

Definition posts_conn_atoms := product_map post_conn_atom.

Fixpoint post_conn_return post atom : partial_return_statement :=
  match post with
  | partial_post_intro P p1 =>
    match atom with atom_return_intro p2 rv =>
      partial_return_intro P (p1 ++ p2) rv end
  | partial_post_binded A HA post' =>
      partial_return_binded A HA 
        (fun x => post_conn_return (post' x) atom)
  end.

Definition posts_conn_returns := product_map post_conn_return.
  

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

Definition posts_conn_pres := product_map post_conn_pre.

  

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


Fixpoint add_pre_to_result (Ppre: assert) (P: assert) (res: split_result) : split_result :=
  match res with
  | split_result_error => split_result_error
  (* | split_result_binded A HA res' =>
      split_result_binded A HA (fun a => add_pre_to_result Ppre P (res' a)) *)
  | split_result_intro res => split_result_intro (add_given_P_to_basic_result Ppre P res)
  end.

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

(**********************************************)
(* combine c1;;c2 split results*)
(**********************************************)

Definition Sseq_split_basic res1 res2 := {|
  pre          := pre res1 ++ atoms_conn_pres (normal_atom res1) (pre res2);
  paths        := paths res1 ++ paths res2 ++ posts_conn_pres (normal_post res1) (pre res2);
  normal_post  := normal_post res2 ++ posts_conn_atoms (normal_post res1) (normal_atom res2);
  continue_post:= continue_post res1 ++ continue_post res2
                  ++ posts_conn_atoms (normal_post res1) (continue_atom res2);
  break_post   := break_post res1 ++ break_post res2
                  ++ posts_conn_atoms (normal_post res1) (break_atom res2);
  return_post  := return_post res1 ++ return_post res2
                  ++ posts_conn_returns (normal_post res1) (return_atom res2);
  normal_atom  := atoms_conn_atoms (normal_atom res1) (normal_atom res2) ;
  continue_atom:= continue_atom res1 ++ atoms_conn_atoms (normal_atom res1) (continue_atom res2) ;
  break_atom   := break_atom res1 ++ atoms_conn_atoms (normal_atom res1) (break_atom res2) ;
  return_atom  := return_atom res1 ++ atoms_conn_returns (normal_atom res1) (return_atom res2) ;
|}.

Fixpoint Sseq_split_aux (res1: split_result_basic) (res2: split_result) : split_result :=
  match res2 with
  | split_result_error => split_result_error
  (* | split_result_binded A HA res2' =>
      split_result_binded A HA (fun a => Sseq_split_aux res1 (res2' a)) *)
  | split_result_intro res2 =>
      split_result_intro (Sseq_split_basic res1 res2)
  end.

Fixpoint Sseq_split (res1 res2: split_result) : split_result :=
  match res1 with
  | split_result_error => split_result_error
  (* | split_result_binded A HA res1' =>
      split_result_binded A HA (fun a => Sseq_split (res1' a) res2) *)
  | split_result_intro res1 => Sseq_split_aux res1 res2      
  end.

(**********************************************)
(* combine if e then c1 else c2 split results *)
(**********************************************)

Definition Sifthenelse_split_basic a res1 res2 := {|
  pre := add_bexp_to_partial_pres a (pre res1) 
            ++ add_bexp_to_partial_pres (Cnot a) (pre res2);
  paths := paths res1 ++ paths res2;
  normal_post := normal_post res1 ++ normal_post res2;
  continue_post := continue_post res1 ++ continue_post res2;
  return_post := return_post res1 ++ return_post res2;
  break_post := break_post res1 ++ break_post res2;
  normal_atom := add_bexp_to_normal_atoms a (normal_atom res1) 
                ++ add_bexp_to_normal_atoms (Cnot a) (normal_atom res2);
  break_atom := add_bexp_to_normal_atoms a (break_atom res1) 
                ++ add_bexp_to_normal_atoms (Cnot a) (break_atom res2);
  return_atom := add_bexp_to_return_atoms a (return_atom res1) 
                ++ add_bexp_to_return_atoms (Cnot a) (return_atom res2);
  continue_atom := add_bexp_to_normal_atoms a (continue_atom res1) 
                ++ add_bexp_to_normal_atoms (Cnot a) (continue_atom res2);
|}.

Fixpoint Sifthenelse_split_aux b (res1: split_result_basic) (res2: split_result) : split_result :=
  match res2 with
  | split_result_error => split_result_error
  (* | split_result_binded A HA res2' =>
      split_result_binded A HA (fun a => Sifthenelse_split_aux b res1 (res2' a)) *)
  | split_result_intro res2 =>
      split_result_intro (Sifthenelse_split_basic b res1 res2)
  end.

Fixpoint Sifthenelse_split b (res1 res2: split_result) : split_result :=
  match res1 with
  | split_result_error => split_result_error
  (* | split_result_binded A HA res1' =>
      split_result_binded A HA (fun a => Sifthenelse_split b (res1' a) res2) *)
  | split_result_intro res1 => Sifthenelse_split_aux b res1 res2      
  end.

(**********************************************)
(* combine [Sloop inv c1 c2] split results *)
(**********************************************)
Definition isnil {A : Type} (l : list A) := 
  match l with
  | [] => true
  | _ :: _ => false
  end.

Definition Sloop_0inv_split_basic res1 res2 :=
  (* there should be some assertion in the loop *)
  if (isnil (pre res1) || isnil (pre res2))%bool then None
  (* continue is not allowed in [c_incr] *)
  else if (negb (isnil (continue_atom res2)) || 
           negb (isnil (continue_post res2)))%bool then None
  (* normal_atom1 + normal_atom2 forms an unannotated loop *)
  else if (isnil (normal_atom res1) && isnil (normal_atom res2))%bool then None
  (* continue_atom1 + normal_atom2 forms an unannotated loop *)
  else if (isnil (continue_atom res1) && isnil (normal_atom res2))%bool then None
  else Some {|
    pre     := pre res1 ++ atoms_conn_pres (normal_atom res1) (pre res2) 
            ++ atoms_conn_pres (continue_atom res1) (pre res2);
    (* path1 ++ path2 ++ nc_post1 * pre2 ++ nc_post1 *n_atom2 * pre1 
        ++ n_post2 * pre1 ++ n_post2 * nc_atom1 * pre2 *) 
    paths   := paths res1 ++ paths res2 ++ posts_conn_pres (normal_post res1) (pre res2) 
            ++ posts_conn_pres (continue_post res1) (pre res2)
            ++ posts_conn_pres (normal_post res2) (pre res1) 
            ++ (posts_conn_pres (posts_conn_atoms (normal_post res1) (normal_atom res2)) (pre res1))
            ++ (posts_conn_pres (posts_conn_atoms (continue_post res1) (normal_atom res2)) (pre res1))
            ++ (posts_conn_pres (posts_conn_atoms (normal_post res2) (normal_atom res1)) (pre res2))
            ++ (posts_conn_pres (posts_conn_atoms (normal_post res2) (continue_atom res1)) (pre res2))
            ;
    normal_post := (break_post res1) ++ (break_post res2) 
                ++ (posts_conn_atoms (normal_post res1) (break_atom res2)) 
                ++ (posts_conn_atoms (normal_post res2) (break_atom res1))
                ++ (posts_conn_atoms (continue_post res1) (break_atom res2)) 
                ++ (posts_conn_atoms (normal_post res2) (atoms_conn_atoms (normal_atom res1) (break_atom res2)))
                ++ (posts_conn_atoms (normal_post res2) (atoms_conn_atoms (continue_atom res1) (break_atom res2)))
                ++ (posts_conn_atoms (normal_post res1) (atoms_conn_atoms (normal_atom res2) (break_atom res1)))
                ++ (posts_conn_atoms (continue_post res1) (atoms_conn_atoms (normal_atom res2) (break_atom res1)));
    continue_post := nil;
    break_post  := nil;
    return_post := (return_post res1) ++ (return_post res2)
                ++ posts_conn_returns(normal_post res1)(return_atom res2) 
                ++ posts_conn_returns(continue_post res1)(return_atom res2)
                ++ posts_conn_returns(normal_post res2)(return_atom res1)
                ++ (posts_conn_returns (normal_post res2) (atoms_conn_returns (normal_atom res1) (return_atom res2)))
                ++ (posts_conn_returns (normal_post res2) (atoms_conn_returns (continue_atom res1) (return_atom res2)))
                ++ (posts_conn_returns (normal_post res1) (atoms_conn_returns (normal_atom res2) (return_atom res1)))
                ++ (posts_conn_returns (continue_post res1) (atoms_conn_returns (normal_atom res2) (return_atom res1)));
    normal_atom := break_atom res1 ++ atoms_conn_atoms (normal_atom res1) (break_atom res2) 
                ++ atoms_conn_atoms (continue_atom res1) (break_atom res2)
                ++ atoms_conn_atoms (normal_atom res2) (break_atom res1);
    continue_atom := nil;
    break_atom    := nil;
    return_atom   := return_atom res1 ++ atoms_conn_returns (normal_atom res1) (return_atom res2) 
                  ++ atoms_conn_returns (continue_atom res1) (return_atom res2)
                  ++ atoms_conn_returns (normal_atom res2) (return_atom res1);
  |}.

Definition Sloop_1inv_split_basic inv res1 res2 :=
  (* continue is not allowed in [c_incr] *)
  if (negb (isnil (continue_atom res2)) || 
      negb (isnil (continue_post res2)))%bool then None
  else Some {|
    pre := [ partial_pre_intro [] inv ];
    paths := 
      add_P_to_partial_pres inv (pre res1) ++
      add_P_to_partial_pres inv (atoms_conn_pres (normal_atom res1) (pre res2)) ++
      add_P_to_partial_pres inv (atoms_conn_pres (normal_atom res1) (add_Q_to_normal_atoms (normal_atom res2) inv)) ++
      add_P_to_partial_pres inv (atoms_conn_pres (continue_atom res1) (add_Q_to_normal_atoms (normal_atom res2) inv)) ++
      add_P_to_partial_pres inv (atoms_conn_pres (continue_atom res1) (pre res2)) ++
      paths res1 ++ paths res2 ++
      posts_conn_pres (normal_post res1) (pre res2) ++
      posts_conn_pres (normal_post res1) (add_Q_to_normal_atoms (normal_atom res2) inv) ++
      posts_conn_pres (continue_post res1) (pre res2) ++
      posts_conn_pres (continue_post res1) (add_Q_to_normal_atoms (normal_atom res2) inv) ++
      add_Q_to_normal_posts (normal_post res2) inv;
    normal_post :=
      break_post res1 ++ break_post res2 ++
      add_P_to_normal_atoms inv (break_atom res1) ++
      add_P_to_normal_atoms inv (atoms_conn_atoms (normal_atom res1) (break_atom res2)) ++
      add_P_to_normal_atoms inv (atoms_conn_atoms (continue_atom res1) (break_atom res2)) ++
      posts_conn_atoms (normal_post res1) (break_atom res2) ++
      posts_conn_atoms (continue_post res1) (break_atom res2);
    continue_post := nil;
    break_post := nil;
    return_post :=
      (return_post res1) ++ (return_post res2) ++
      add_P_to_return_atoms inv (return_atom res1) ++
      add_P_to_return_atoms inv (atoms_conn_returns (normal_atom res1) (return_atom res2)) ++
      add_P_to_return_atoms inv (atoms_conn_returns (continue_atom res1) (return_atom res2)) ++
      posts_conn_returns (normal_post res1) (return_atom res2) ++
      posts_conn_returns (continue_post res1) (return_atom res2) ;
    normal_atom := nil;
    break_atom := nil;
    continue_atom := nil;
    return_atom := nil
        (* no continue condition in c2 *)
  |}.


Definition Sloop_2inv_split_basic inv1 inv2 res1 res2 :=
  (* continue is not allowed in [c_incr] *)
  if (negb (isnil (continue_atom res2)) || 
      negb (isnil (continue_post res2)))%bool then None
  else Some {|
    pre := [ partial_pre_intro [] inv1 ];
    paths := 
      add_P_to_partial_pres inv1 (pre res1) ++
      add_P_to_partial_pres inv1 (add_Q_to_normal_atoms (normal_atom res1) inv2) ++
      add_P_to_partial_pres inv1 (add_Q_to_normal_atoms (continue_atom res1) inv2) ++
      add_Q_to_normal_posts (normal_post res1) inv2 ++
      add_Q_to_normal_posts (continue_post res1) inv2 ++
      add_P_to_partial_pres inv2 (pre res2) ++
      add_P_to_partial_pres inv2 (add_Q_to_normal_atoms (normal_atom res2) inv1) ++
      add_Q_to_normal_posts (normal_post res2) inv1 ++
      add_Q_to_normal_posts (continue_post res2) inv1 ++
      paths res1 ++ paths res2;
    normal_post :=
      break_post res1 ++ break_post res2 ++
      add_P_to_normal_atoms inv1 (break_atom res1) ++
      add_P_to_normal_atoms inv2 (break_atom res2);
    continue_post := nil;
    break_post := nil;
    return_post :=
      (return_post res1) ++ (return_post res2) ++
      add_P_to_return_atoms inv1 (return_atom res1) ++
      add_P_to_return_atoms inv2 (return_atom res2) ;
    normal_atom := nil;
    break_atom := nil;
    continue_atom := nil;
    return_atom := nil
      (* no continue condition in c2 *)
|}.

Definition Sloop_split_basic inv res1 res2 := 
  match inv with
  | LINull => Sloop_0inv_split_basic res1 res2
  | LISingle inv => Sloop_1inv_split_basic inv res1 res2
  | LIDouble inv1 inv2 => Sloop_2inv_split_basic inv1 inv2 res1 res2
  end.


Fixpoint Sloop_split_aux inv (res1: split_result_basic) (res2: split_result) : split_result :=
  match res2 with
  | split_result_error => split_result_error
  (* | split_result_binded A HA res2' =>
      split_result_binded A HA (fun a => Sloop_split_aux inv res1 (res2' a)) *)
  | split_result_intro res2 =>
      match (Sloop_split_basic inv res1 res2) with
      | Some res => split_result_intro res
      | None => split_result_error
      end
  end.

Fixpoint Sloop_split inv (res1 res2: split_result) : split_result :=
  match res1 with
  | split_result_error => split_result_error
  (* | split_result_binded A HA res1' =>
      split_result_binded A HA (fun a => Sloop_split inv (res1' a) res2) *)
  | split_result_intro res1 => Sloop_split_aux inv res1 res2      
  end.



Function split_pre (stm: Split.statement) : option (list partial_pre_statement) := 
  match stm with
  | Sassert a             => Some [ partial_pre_intro [] a ] 
  | Stopgiven A a stm'    => Some []
  | Sgiven A a ass' stm'  => Some []
  | Sassign e1 e2         => Some []
  | Sset i e              => Some []
  | Sskip                 => Some []
  | Sbreak                => Some []
  | Scontinue             => Some []
  | Sreturn rv            => Some []
  | Ssequence s1 s2       =>
      match split_result s1, split_result s2 with
      | Some res1, Some res2 => Some (
          pre res1 ++
          atoms_conn_pres (normal_atom res1) (pre res2)    
      )
      | _, _ => None
      end

  | Sifthenelse e s1 s2   =>
    match split_result s1, split_result s2 with
    | Some res1, Some res2 => Some (
        add_bexp_to_partial_pres e (pre res1) 
        ++ add_bexp_to_partial_pres (Cnot e) (pre res2)
    )
    | _, _ => None
    end

  | Sloop LINull s1 s2       =>
      None
  | Sloop (LISingle inv) s1 s2       =>
      None
  | Sloop (LIDouble inv1 inv2) s1 s2       =>
      None
  
  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end

with split_result (stm: Split.statement) : option split_result_basic :=
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
  end


with split_path (stm: Split.statement) : option (list path_statement) :=
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
      match split_result s1, split_result s2 with
      | Some res1, Some res2 => Some (
      paths res1 ++ 
      paths res2 ++ 
      posts_conn_pres (normal_post res1) (pre res2)
      )
      | _, _ => None
      end
  | Sifthenelse e s1 s2   =>
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
  paths res1 ++ paths res2
    )
    | _, _ => None
    end

  | Sloop LINull s1 s2       =>
      None
  | Sloop (LISingle inv) s1 s2       =>
      None
  | Sloop (LIDouble inv1 inv2) s1 s2       =>
      None
  
  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end

with split_normal_post (stm: Split.statement) : option (list partial_post_statement) :=
  match stm with
  | Sassert a             => Some [ partial_post_intro a []]
  | Stopgiven A a stm'    => Some [] 
  | Sgiven A a ass' stm'  => Some []
  | Sassign e1 e2         => Some []
  | Sset i e              => Some []
  | Sskip                 => Some []
  | Sbreak                => Some []
  | Scontinue             => Some []
  | Sreturn rv            => Some []
  | Ssequence s1 s2       =>
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
      normal_post res2 ++
      posts_conn_atoms (normal_post res1) (normal_atom res2)
      )
      | _, _ => None
      end
  | Sifthenelse e s1 s2   =>
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
  normal_post res1 ++ normal_post res2
    )
    | _, _ => None
    end

  | Sloop LINull s1 s2       =>
      None
  | Sloop (LISingle inv) s1 s2       =>
      None
  | Sloop (LIDouble inv1 inv2) s1 s2       =>
      None
  
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
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
      continue_post res1 ++ continue_post res2
      ++ posts_conn_atoms (normal_post res1) (continue_atom res2)
      )
      | _, _ => None
      end
  | Sifthenelse e s1 s2   =>
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
  continue_post res1 ++ continue_post res2
    )
    | _, _ => None
    end

  | Sloop LINull s1 s2       =>
      None
  | Sloop (LISingle inv) s1 s2       =>
      None
  | Sloop (LIDouble inv1 inv2) s1 s2       =>
      None
  
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
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
      break_post res1 ++ break_post res2
      ++ posts_conn_atoms (normal_post res1) (break_atom res2)
      )
      | _, _ => None
      end
  | Sifthenelse e s1 s2   =>
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
  break_post res1 ++ break_post res2
    )
    | _, _ => None
    end

  | Sloop LINull s1 s2       =>
      None
  | Sloop (LISingle inv) s1 s2       =>
      None
  | Sloop (LIDouble inv1 inv2) s1 s2       =>
      None
  
  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end

with split_return_post (stm: Split.statement) : option (list partial_return_statement) :=
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
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
      return_post res1 ++ return_post res2
      ++ posts_conn_returns (normal_post res1) (return_atom res2)
      )
      | _, _ => None
      end
  | Sifthenelse e s1 s2   =>
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
  return_post res1 ++ return_post res2
    )
    | _, _ => None
    end

  | Sloop LINull s1 s2       =>
      None
  | Sloop (LISingle inv) s1 s2       =>
      None
  | Sloop (LIDouble inv1 inv2) s1 s2       =>
      None
  
  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end

with split_normal_atom (stm: Split.statement) : option (list atom_normal_statement) :=
  match stm with
  | Sassert a             => Some []
  | Stopgiven A a stm'    => Some [] 
  | Sgiven A a ass' stm'  => Some []
  | Sassign e1 e2         => Some [ atom_normal_intro [ inr (ASassign e1 e2) ] ]
  | Sset i e              => Some [ atom_normal_intro [ inr (ASset i e) ] ]
  | Sskip                 => Some [ atom_normal_intro [] ]
  | Sbreak                => Some []
  | Scontinue             => Some []
  | Sreturn rv            => Some []
  | Ssequence s1 s2       => 
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
      atoms_conn_atoms (normal_atom res1) (normal_atom res2)
      )
      | _, _ => None
      end
  | Sifthenelse e s1 s2   =>
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
  add_bexp_to_normal_atoms e (normal_atom res1) 
  ++ add_bexp_to_normal_atoms (Cnot e) (normal_atom res2)
    )
    | _, _ => None
    end

  | Sloop LINull s1 s2       =>
      None
  | Sloop (LISingle inv) s1 s2       =>
      None
  | Sloop (LIDouble inv1 inv2) s1 s2       =>
      None
  
  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end

with split_continue_atom (stm: Split.statement) : option (list atom_normal_statement) :=
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
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
  continue_atom res1 ++ atoms_conn_atoms (normal_atom res1) (continue_atom res2)
  )
  | _, _ => None
  end
  | Sifthenelse e s1 s2   =>
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
  add_bexp_to_normal_atoms e (continue_atom res1) 
  ++ add_bexp_to_normal_atoms (Cnot e) (continue_atom res2)
    )
    | _, _ => None
    end

  | Sloop LINull s1 s2       =>
      None
  | Sloop (LISingle inv) s1 s2       =>
      None
  | Sloop (LIDouble inv1 inv2) s1 s2       =>
      None
  
  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end

with split_break_atom (stm: Split.statement) : option (list atom_normal_statement) :=
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
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
  break_atom res1 ++ atoms_conn_atoms (normal_atom res1) (break_atom res2) 
  )
  | _, _ => None
  end
  | Sifthenelse e s1 s2   =>
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
  add_bexp_to_normal_atoms e (break_atom res1) 
  ++ add_bexp_to_normal_atoms (Cnot e) (break_atom res2)
    )
    | _, _ => None
    end

  | Sloop LINull s1 s2       =>
      None
  | Sloop (LISingle inv) s1 s2       =>
      None
  | Sloop (LIDouble inv1 inv2) s1 s2       =>
      None
  
  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end

with split_return_atom (stm: Split.statement) : option (list atom_return_statement) :=
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
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
  return_atom res1 ++ atoms_conn_returns (normal_atom res1) (return_atom res2)
  )
  | _, _ => None
  end
  | Sifthenelse e s1 s2   =>
  match split_result s1, split_result s2 with
  | Some res1, Some res2 => Some (
  add_bexp_to_return_atoms e (return_atom res1) 
  ++ add_bexp_to_return_atoms (Cnot e) (return_atom res2)
    )
    | _, _ => None
    end

  | Sloop LINull s1 s2       =>
      None
  | Sloop (LISingle inv) s1 s2       =>
      None
  | Sloop (LIDouble inv1 inv2) s1 s2       =>
      None
  
  (* below are unimplemented commands *)
  | Scall i e args        =>    None
  | Sbuiltin i ef tylis args => None
  | _                     =>    None
  end
.
with is_0inv_valid (stm1 stm2: Split.statement) : bool :=
  if (isnil (pre res1) || isnil (pre res2))%bool then false
  (* continue is not allowed in [c_incr] *)
  else if (negb (isnil (continue_atom res2)) || 
          negb (isnil (continue_post res2)))%bool then false
  (* normal_atom1 + normal_atom2 forms an unannotated loop *)
  else if (isnil (normal_atom res1) && isnil (normal_atom res2))%bool then false
  (* continue_atom1 + normal_atom2 forms an unannotated loop *)
  else if (isnil (continue_atom res1) && isnil (normal_atom res2))%bool then false
  else true

with is_12inv_valid (stm1 stm2: Split.statement) : bool :=
  ((isnil (continue_atom res2)) && negb (isnil (continue_post res2)))%bool
.





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



Fixpoint split_hint (stm: Split.statement) : split_result :=
  match stm with
  | Sassert a => split_result_intro (Sassert_split a)
  | Stopgiven A a stm'
    (**r Given a:A,
            ...stm'(a)
    *) => 
      split_result_binded A (inhabits a) (fun a => split_hint (stm' a))
  | Sgiven A a ass' stm'
    (**r {{ EX a:A, ...assert(a) }}
         Given a:A,
            ...statement(a)
    *) => 
      split_result_binded A (inhabits a) (fun a => 
        let Ppre := exp ass' in
        let P := ass' a in
        let stm := stm' a in
        let res := split_hint stm in
          add_pre_to_result Ppre P res
      )
  | Sskip => split_result_intro Sskip_split
  | Sassign e1 e2 (**r assignment [lvalue = rvalue] *)
      => split_result_intro (Sassign_split e1 e2)
  | Sset i e (**r assignment [tempvar = rvalue] *)
      => split_result_intro (Sset_split i e)
  | Ssequence s1 s2 (**r sequence *)
      => Sseq_split (split_hint s1) (split_hint s2)
  | Sifthenelse e s1 s2 (**r conditional *)
      => Sifthenelse_split e (split_hint s1) (split_hint s2)
  | Sloop inv s1 s2  (**r infinite loop *) 
      => Sloop_split inv (split_hint s1) (split_hint s2)
  | Sbreak (**r [break] statement *)
      => split_result_intro Sbreak_split
  | Scontinue (**r [continue] statement *)
      => split_result_intro Scontinue_split
  | Sreturn rv (**r [return] statement *)
      => split_result_intro (Sreturn_split rv)
  (* below are unimplemented commands *)
  | Scall i e args (**r function call *)
      => split_result_error
  | Sbuiltin i ef tylis args (**r builtin invocation *)
      => split_result_error
  | _ => split_result_error
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