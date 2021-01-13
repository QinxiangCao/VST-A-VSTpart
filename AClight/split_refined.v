Require Import AClight.AClight.
Require Export VST.veric.base.
Require Export VST.veric.SeparationLogic.
Require Export VST.msl.Extensionality.
Require Export compcert.lib.Coqlib.
Require Export VST.msl.Coqlib2 VST.veric.coqlib4 VST.floyd.coqlib3.
Require Export VST.veric.juicy_extspec.
Require Import VST.veric.NullExtension.
Require Export VST.floyd.jmeq_lemmas.
Require Export VST.floyd.find_nth_tactic.
Require Export VST.floyd.val_lemmas.
Require Export VST.floyd.assert_lemmas.
Require Import VST.veric.semax_lemmas.
Require VST.floyd.SeparationLogicAsLogicSoundness.
Export SeparationLogicAsLogicSoundness.MainTheorem.CSHL_Sound.DeepEmbedded.
Require Import VST.floyd.proofauto.
Notation "x ;; y" := (Ssequence x y)  (at level 65) : logic.

Axiom classic: forall P,  P \/ ~ P.



Inductive atom_statement : Type :=
| Sskip : atom_statement                   (**r do nothing *)
| Sassign : expr -> expr -> atom_statement (**r assignment [lvalue = rvalue] *)
| Sset : ident -> expr -> atom_statement   (**r assignment [tempvar = rvalue] *)
| Scall: option ident -> expr -> list expr -> atom_statement (**r function call *)
(*| Sbreak : atom_statement                      (**r [break] statement *)
| Scontinue : atom_statement                   (**r [continue] statement *)
| Sreturn : option expr -> atom_statement      (**r [return] statement *)
*). 

Definition path:= list (expr + atom_statement) .

Definition Non_empty_Type (A:Type): Prop := exists a:A, True.


Inductive split_assert: Type :=
| Basic_assert : assert -> assert -> split_assert
| Given_assert (A:Type) (HA: Non_empty_Type A ): (A -> split_assert) -> split_assert
| Binded_assert (A:Type) (HA: Non_empty_Type A ): (A -> split_assert) -> split_assert.

Definition path_statement : Type :=
  split_assert * path.

Inductive partial_assert: Type :=
| Basic_partial : assert  -> partial_assert
| Binded_partial (A:Type) (HA: Non_empty_Type A ) :
    (A -> partial_assert) -> partial_assert.

Definition partial_path_statement : Type :=
  partial_assert * path.

Definition return_post_statement : Type := 
  partial_assert * path * option expr.

Definition return_path_atom : Type := path * option expr.

Definition path_statements := list path_statement.
Definition partial_path_statements := list partial_path_statement.
Definition return_post_statements := list return_post_statement.
Definition atom_statements := (list path)%type.
Definition return_atom_statements := (list return_path_atom)%type.

Record split_result:Type := Pack{
  pre   : partial_path_statements;
  paths : path_statements;
  normal_post  : partial_path_statements;
  continue_post: partial_path_statements;
  break_post   : partial_path_statements;
  return_post  : return_post_statements;
  normal_atom  : atom_statements;
  continue_atom: atom_statements;
  break_atom   : atom_statements;
  return_atom  : return_atom_statements;
}.

(**
-----------------------------------------------------------------------------
  Combine two single unit as a new one , four situations 
-----------------------------------------------------------------------------
**)


Definition FALSE := (PROP (False) LOCAL () SEP ()).

Fixpoint basic_assert_conn_bind (a1:assert) (a2: partial_assert) : split_assert :=
  match a2 with
  | Basic_partial a2 => (Basic_assert a1 a2)
  | Binded_partial X HX a2' => (Given_assert X HX (fun x:X => basic_assert_conn_bind
                                                             a1 (a2' x)))
  end.

Fixpoint bind_assert_conn_basic (a2:assert) (a1: partial_assert) : split_assert :=
  match a1 with
  | Basic_partial a1 => (Basic_assert a1 a2)
  | Binded_partial X HX a1' => (Given_assert X HX (fun x:X => bind_assert_conn_basic
                                                            a2 (a1' x)))
  end.


Definition post_conn_bind_pre (pre:partial_path_statement) (p1: path) (a1: assert): path_statement :=
  match pre with (a2, p2) =>
    (basic_assert_conn_bind a1 a2, p1 ++ p2)
  end.


Fixpoint bind_post_conn_pre (post: partial_path_statement) (p2: path) (a2: assert): path_statement :=
  match post with (a1, p1) =>
                  (bind_assert_conn_basic a2 a1, p1 ++ p2)
  end.


Fixpoint posts_conn_pre (posts: partial_path_statements) (pre:partial_path_statement): path_statements :=
  (* posts  + pre, posts have to be basic, pre can be binded*)
  match posts with
  | (Basic_partial a1, p1)::posts' =>
    match p1, pre with
    | [], (Binded_partial _ _ _, _) =>
      (post_conn_bind_pre pre p1 a1)::(posts_conn_pre posts' pre)
    | _, (Basic_partial _, _) =>
      (post_conn_bind_pre pre p1 a1)::(posts_conn_pre posts' pre)
    | _, _  => (posts_conn_pre posts' pre)
    end
  | (Binded_partial X HX a1, p1)::posts' =>
    match pre with
    | (Basic_partial a2, p2) =>
      (bind_post_conn_pre (Binded_partial X HX a1, p1) p2 a2)
        ::(posts_conn_pre posts' pre)
    | _ => posts_conn_pre posts' pre
    end
  | nil => nil
  end.

Definition posts_conn_pres (posts pres: partial_path_statements) : path_statements :=
  flat_map (posts_conn_pre posts) pres.

(* 
    Double check p1 should be empty,
    and deal with EX in the assert when defining Semax(path_statement)
*) 

Definition post_conn_atom (post:partial_path_statement) (p2: path): partial_path_statement :=
  match post with (a1, p1) =>
    (a1, p1 ++ p2)
  end.

Definition post_conn_return (post:partial_path_statement) (p2: path) (r: option expr): return_post_statement :=
  match post with (a1, p1) =>
    (a1, p1 ++ p2, r)
  end.

Definition posts_conn_returns (posts: partial_path_statements) (rets: return_atom_statements) :
  return_post_statements :=
  flat_map (fun post => 
    map (
      fun ret_atom => post_conn_return post (fst ret_atom) (snd ret_atom)) rets
  ) posts.

Definition posts_conn_atoms (posts: partial_path_statements) (atoms: atom_statements) :
partial_path_statements :=
flat_map (fun post => 
  map (post_conn_atom post) atoms
) posts.

Definition atom_conn_pre (p1:path) (pre: partial_path_statement) : partial_path_statement:=
  match pre with (a2, p2) =>
    (a2, p1 ++ p2)
  end.

Definition atoms_conn_pres (atoms: atom_statements) (pres: partial_path_statements) :
partial_path_statements :=
flat_map (fun atom => 
  map (atom_conn_pre atom) pres
) atoms.

Definition atoms_conn_atoms (atom1: atom_statements)
 (atom2: atom_statements) : atom_statements :=
   flat_map (fun p1 => map (app p1) atom2) atom1.

Definition atoms_conn_returns (atom1: atom_statements)
 (atom2: return_atom_statements) : return_atom_statements :=
   flat_map (fun p1 => 
      map (fun ret_atom =>
          (p1++(fst ret_atom),snd ret_atom)) atom2) atom1.

(**
-----------------------------------------------------------------------------
  Add the expr as a singleton 'path' to paths. Used in if branch.
    updated : also used in do-while loop.
  Two main situations : adding to a (path * assert) , or to a (path) 
    
-----------------------------------------------------------------------------
**)

Fixpoint add_bexp_to_path (s: partial_path_statement) (e:expr) : partial_path_statement :=
  match s with (a, p) =>
    (a, (inl e)::p)
  end.

Inductive basic_split : statement -> split_result->Prop :=

| (* It is equivalent to a singleton of path : [[inr (Sset ident exp) ]] *)
  Split_set : forall ident exp,
  basic_split ((AClight.Sset ident exp)) 
    (Pack nil nil nil nil nil nil [[inr (Sset ident exp) ]] nil nil nil )
        
| (* it is just a singleton too. Therefore only the normal_atom will be not empty *) 
  Split_assign : forall exp1 exp2,
  basic_split (AClight.Sassign exp1 exp2)
    (Pack nil nil nil nil nil nil [[inr (Sassign exp1 exp2)]] nil nil nil )

| (* pre and normal_post not empty*) 
  Split_assert : forall a,
  basic_split (Sassert a) 
  (Pack [(Basic_partial a, nil)] nil [(Basic_partial a, nil)] nil nil nil nil nil nil nil)

| Split_continue : 
  basic_split AClight.Scontinue (Pack nil nil nil nil nil nil nil [nil] nil nil)

| Split_break : 
  basic_split AClight.Sbreak (Pack nil nil nil nil nil nil nil nil [nil] nil)

| Split_Sskip : 
  basic_split AClight.Sskip (Pack nil nil nil nil nil nil [nil] nil nil nil)

| Split_Sreturn : forall val ,
  basic_split (AClight.Sreturn val)
  (Pack nil nil nil nil nil nil nil nil nil [(nil,val)])
 
| Split_func : forall ident e el,
  basic_split (AClight.Scall (ident) e el)
  (Pack nil nil nil nil nil nil [[inr (Scall (ident) e el)]] nil nil nil)
  .

Inductive bind_partial_add (X:Type) (HX: Non_empty_Type X ):
  partial_path_statements -> (X -> partial_path_statements) -> Prop :=
| bind_partial_nil: bind_partial_add X HX nil (fun _ => nil)
| bind_partial_cons: forall p1 tl1 tl2 a,
    bind_partial_add X HX tl1 tl2 ->
    bind_partial_add X HX ((Binded_partial X HX a, p1)::tl1)
                     (fun x:X => ((a x, p1)::(tl2 x)))
.

Inductive bind_return_add (X:Type) (HX: Non_empty_Type X ):
  return_post_statements -> (X -> return_post_statements) -> Prop :=
| bind_return_nil: bind_return_add X HX nil (fun _ => nil)
| bind_return_cons: forall p1 tl1 tl2 a v,
    bind_return_add X HX tl1 tl2 ->
    bind_return_add X HX ((Binded_partial X HX a, p1, v)::tl1)
                    (fun x:X => ((a x, p1, v)::(tl2 x)))
.

Inductive bind_path_add (X:Type) (HX: Non_empty_Type X ):
  path_statements -> (X -> path_statements) -> Prop :=
| bind_path_nil: bind_path_add X HX nil (fun _ => nil)
| bind_path_cons: forall p1 tl1 tl2 a,
    bind_path_add X HX tl1 tl2 ->
    bind_path_add X HX ((Binded_assert X HX a, p1)::tl1)
                    (fun x:X => ((a x, p1)::(tl2 x)))
.

Fixpoint bind_partial_add'(A:Type) (partials:partial_path_statements): A -> partial_path_statements :=
  match partials with
  | nil => (fun _ => nil)
  | partial :: tl => (fun a:A => (partial)::(bind_partial_add' A tl a))
  end.  

Inductive AClight_to_Clight : AClight.statement -> Clight.statement -> Prop :=
| to_Clight_assert: forall a,
    AClight_to_Clight (Sassert a) Clight.Sskip
| to_Clight_dummyassert: forall a,
    AClight_to_Clight (Sdummyassert a) Clight.Sskip
| to_Clight_given: forall (A:Type) (HA:Non_empty_Type A) stm c_stm,
    (forall a, AClight_to_Clight (stm a) c_stm) ->
    AClight_to_Clight  (Sgiven A stm) c_stm
| to_Clight_local: forall a1 n a2 stm c_stm,
    AClight_to_Clight  stm c_stm ->
    AClight_to_Clight (Slocal a1 n stm a2) c_stm
| to_Clight_skip:
    AClight_to_Clight AClight.Sskip Clight.Sskip
| to_Clight_assign: forall e1 e2,
    AClight_to_Clight (AClight.Sassign e1 e2) (Clight.Sassign e1 e2)
| to_Clight_set: forall id e,
    AClight_to_Clight (AClight.Sset id e) (Clight.Sset id e)
| to_Clight_builtin: forall id f tlis e,
    AClight_to_Clight (Sbuiltin id f tlis e) (Clight.Sbuiltin id f tlis e)
| to_Clight_call: forall id e elis,
    AClight_to_Clight (AClight.Scall id e elis) (Clight.Scall id e elis)
| to_Clight_sequence: forall stm1 c_stm1 stm2 c_stm2,
    AClight_to_Clight stm1 c_stm1 ->
    AClight_to_Clight stm2 c_stm2 ->
    AClight_to_Clight (Ssequence stm1 stm2) (Clight.Ssequence c_stm1 c_stm2)
| to_Clight_ifthenelse: forall e stm1 c_stm1 stm2 c_stm2,
    AClight_to_Clight stm1 c_stm1 ->
    AClight_to_Clight stm2 c_stm2 ->
    AClight_to_Clight (Sifthenelse e stm1 stm2) (Clight.Sifthenelse e c_stm1 c_stm2)
| to_Clight_loop: forall inv stm1 c_stm1 stm2 c_stm2,
    AClight_to_Clight stm1 c_stm1 ->
    AClight_to_Clight stm2 c_stm2 ->
    AClight_to_Clight (Sloop inv stm1 stm2) (Clight.Sloop c_stm1 c_stm2)
| to_Clight_break:
    AClight_to_Clight AClight.Sbreak Clight.Sbreak
| to_Clight_continue:
    AClight_to_Clight AClight.Scontinue Clight.Scontinue
| to_Clight_return: forall e,
    AClight_to_Clight (AClight.Sreturn e) (Clight.Sreturn e)
| to_Clight_switch: forall e ls c_ls,
    to_Clight_seq ls c_ls ->
    AClight_to_Clight (Sswitch e ls) (Clight.Sswitch e c_ls)
| to_Clight_label: forall id stm c_stm,
    AClight_to_Clight stm c_stm ->
    AClight_to_Clight (Slabel id stm) (Clight.Slabel id c_stm)
| to_Clight_goto: forall id,
    AClight_to_Clight (Sgoto id) (Clight.Sgoto id)

with to_Clight_seq : labeled_statements -> Clight.labeled_statements -> Prop :=
| to_Clight_seq_nil: to_Clight_seq LSnil Clight.LSnil
| to_Clight_seq_cons: 
    forall z stm c_stm seq c_seq,
      AClight_to_Clight stm c_stm ->
      to_Clight_seq seq c_seq ->
      to_Clight_seq (LScons z stm seq)
        (Clight.LScons z c_stm c_seq).


Lemma AClight_to_Clight_unique: forall stm c_stm1 c_stm2,
  AClight_to_Clight stm c_stm1 ->
  AClight_to_Clight stm c_stm2 ->
  c_stm1 = c_stm2.
Proof.
  intros. generalize dependent c_stm1.
  generalize dependent c_stm2.
  induction stm; intros;
  try (inv H0; inv H; auto).
  - inv H0. inv H1. destruct HA as [a _]. specialize (H a).
    apply inj_pair2 in H4. apply inj_pair2 in H3. subst.
    apply H; auto. 
  - specialize (IHstm1 _ H2 _ H3).
    specialize (IHstm2 _ H5 _ H6). subst. auto.
  - specialize (IHstm1 _ H4 _ H5).
    specialize (IHstm2 _ H7 _ H6). subst. auto.
  - specialize (IHstm1 _ H4 _ H5).
    specialize (IHstm2 _ H6 _ H7). subst. auto.
  - admit.
  - specialize (IHstm _ H4 _ H3). subst. auto.
Admitted.


Inductive bind_result_add (A:Type) (HA: Non_empty_Type A ):
  split_result -> (A -> split_result) -> Prop := 
| bind_result_add_intro: forall pre paths normal_post break_post 
    continue_post return_post normal_atom break_atom continue_atom
    return_atom pre' paths' normal_post' break_post'
    continue_post' return_post',
    bind_partial_add A HA pre pre' ->
    bind_partial_add A HA normal_post normal_post' ->
    bind_partial_add A HA break_post break_post' ->
    bind_partial_add A HA continue_post continue_post' ->
    bind_return_add A HA return_post return_post' ->
    bind_path_add A HA paths paths' ->
    bind_result_add A HA (Pack pre paths normal_post break_post continue_post
                            return_post normal_atom break_atom continue_atom
                            return_atom)
                      (fun a:A => Pack (pre' a) (paths' a) (normal_post' a) (break_post' a) (continue_post' a) (return_post' a) normal_atom break_atom continue_atom
                      return_atom)
.



Fixpoint all_basic (pres: list partial_path_statement) :=
  match pres with
  | (Binded_partial _ _  _, _)::_ => false
  | (Basic_partial _, _):: tl => all_basic tl
  | nil => true
  end.

Fixpoint all_empty_path (posts: list partial_path_statement) :=
  match posts with
  | (_, _ :: _)::_ => false
  | (_, nil):: tl => all_empty_path tl
  | nil => true
  end.


Fixpoint all_empty_atom (posts: list path) :=
  match posts with
  | ( _ :: _)::_ => false
  | ( nil):: tl => all_empty_atom tl
  | nil => true
  end.

Definition add_exp_to_pre e (pre:partial_path_statement) :=
  match pre with
  | (a, p) => (a, (inl e)::p)
  end.

Definition add_exp_to_pres e pres :=
  map (add_exp_to_pre e) pres.

Definition add_exp_to_atoms e (atoms:atom_statements) :=
  map (cons (inl e)) atoms.

Definition add_exp_to_return_atom e (ret_atom:return_path_atom):=
  match ret_atom with
  | (p, r) => ((inl e)::p, r)
  end.

Definition add_exp_to_return_atoms e ret_atoms := 
  map (add_exp_to_return_atom e) ret_atoms.


Fixpoint pack_assert_into_post_assert Q (P:partial_assert) :=
  match P with
  | Basic_partial a1 => Basic_assert a1 Q
  | Binded_partial X HX P' => Binded_assert X HX 
                              (fun x => pack_assert_into_post_assert Q (P' x))
  end.

Definition pack_assert_into_post Q (post:partial_path_statement) :=
  match post with (P, p) =>
  (pack_assert_into_post_assert Q P, p)
  end.

Definition pack_assert_into_posts Q posts :=
  map (pack_assert_into_post Q) posts.


Inductive path_split: statement -> split_result -> Prop :=
| (* Given A, c(A) *)
  split_given: forall (X: Type)(HX:Non_empty_Type X)
    (stm': X -> statement) res' res,  
    bind_result_add X HX res res' -> 
    (forall x:X, path_split (stm' x) (res' x)) ->
    path_split (Sgiven X stm') res
| (* c1 ;; c2 *)
  split_seq: forall stm1 stm2 res1 res2,
    path_split stm1 res1 ->
    path_split stm2 res2 ->
    ((all_basic (pre res2) = true) (* __ ;; basic *)  \/
    ((* basic ;; bind*)
      (all_basic(normal_post res1) = true)/\
      (all_empty_path (normal_post res1)=true)/\
      (all_empty_atom (normal_atom res1)=true)
    ))
    ->
    path_split (stm1;;stm2)
      ({|
        pre := pre res1 ++ atoms_conn_pres (normal_atom res1) (pre res2);
        paths := paths res1 ++ paths res2 ++ posts_conn_pres (normal_post res1) (pre res2);
        normal_post := normal_post res2 ++ posts_conn_atoms (normal_post res1) (normal_atom res2);
        continue_post := continue_post res1 ++ continue_post res2
                          ++ posts_conn_atoms (normal_post res1) (continue_atom res2);
        break_post := break_post res1 ++ break_post res2
                          ++ posts_conn_atoms (normal_post res1) (break_atom res2);
        return_post := return_post res1 ++ return_post res2
                          ++ posts_conn_returns (normal_post res1) (return_atom res2);
        normal_atom := atoms_conn_atoms (normal_atom res1) (normal_atom res2);
        return_atom := return_atom res1 ++ atoms_conn_returns (normal_atom res1) (return_atom res2);
        break_atom := break_atom res1 ++ atoms_conn_atoms (normal_atom res1) (break_atom res2);
        continue_atom := continue_atom res1 ++ atoms_conn_atoms (normal_atom res1) (continue_atom res2);
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
      pre := add_exp_to_pres a (pre res1) ++ add_exp_to_pres (Cnot a) (pre res2);
      paths := paths res1 ++ paths res2;
      normal_post := normal_post res1 ++ normal_post res2;
      continue_post := continue_post res1 ++ continue_post res2;
      return_post := return_post res1 ++ return_post res2;
      break_post := break_post res1 ++ break_post res2;
      normal_atom := add_exp_to_atoms a (normal_atom res1) 
                    ++ add_exp_to_atoms (Cnot a) (normal_atom res2);
      break_atom := add_exp_to_atoms a (break_atom res1) 
                    ++ add_exp_to_atoms (Cnot a) (break_atom res2);
      return_atom := add_exp_to_return_atoms a (return_atom res1) 
                    ++ add_exp_to_return_atoms (Cnot a) (return_atom res2);
      continue_atom := add_exp_to_atoms a (continue_atom res1) 
                    ++ add_exp_to_atoms (Cnot a) (continue_atom res2);
    |}
| Split_loop_double: forall inv1 inv2 c1 c2 res1 res2 
  (Econt_atom: continue_atom res2 = [])
  (Econt_post: continue_post res2 = [])
  (* (Ebasic_normal1: all_basic (normal_post res1)= true)
  (Ebasic_continue1: all_basic (continue_post res1)= true)
  (Ebasic_pre2: all_basic (pre res2)= true) *) ,
    path_split c1 res1 ->
    path_split c2 res2 ->
    path_split (Sloop (LIDouble inv1 inv2) c1 c2) {|
      pre := [(Basic_partial inv1,nil)];
      paths := 
        posts_conn_pres [(Basic_partial inv1, nil)] (pre res1) ++
        posts_conn_pres [(Basic_partial inv1, nil)]
          (atoms_conn_pres (normal_atom res1) [(Basic_partial inv2, nil)]) ++
        posts_conn_pres [(Basic_partial inv1, nil)]
          (atoms_conn_pres (continue_atom res1) [(Basic_partial inv2, nil)]) ++
        pack_assert_into_posts inv2 (normal_post res1) ++
        pack_assert_into_posts inv2 (continue_post res1) ++
        posts_conn_pres [(Basic_partial inv2, nil)] (pre res2) ++
        posts_conn_pres [(Basic_partial inv2, nil)]
          (atoms_conn_pres (normal_atom res2) [(Basic_partial inv1, nil)]) ++
        pack_assert_into_posts inv1 (normal_post res2) ++
        pack_assert_into_posts inv1 (continue_post res2) ++
        paths res1 ++ paths res2;
      normal_post :=
        break_post res1 ++ break_post res2 ++
        posts_conn_atoms [(Basic_partial inv1, nil)] (break_atom res1) ++
        posts_conn_atoms [(Basic_partial inv2, nil)] (break_atom res2);
      continue_post := nil;
      break_post := nil;
      return_post :=
        (return_post res1) ++ (return_post res2) ++
        posts_conn_returns [(Basic_partial inv1, nil)] (return_atom res1) ++
        posts_conn_returns [(Basic_partial inv2, nil)] (return_atom res2) ;
      normal_atom := nil;
      break_atom := nil;
      continue_atom := nil;
      return_atom := nil
          (* no continue condition in c2 *)
    |}
  | split_loop_single_skip: forall inv c1 c1' c2 c2' res,
      AClight_to_Clight c1 c1' ->
      AClight_to_Clight c2 c2' ->
      nocontinue c2' = true ->
      nocontinue c1' = true \/ c2 = AClight.Sskip ->
      path_split (Sloop (LIDouble inv inv) (c1;;c2) AClight.Sskip) res ->
      path_split (Sloop (LISingle inv) c1 c2) res
  
| Split_loop_null: forall stm1 stm2 res1 res2
  (Econt_atom: continue_atom res2 = [])
  (Econt_post: continue_post res2 = [])
  (Ebasic_pre1: all_basic (pre res1) = true)
  (Ebasic_pre2: all_basic (pre res2) = true),
  (pre res1 <> [] \/ pre res2 <> [])->
  (normal_atom res1 = [] \/ normal_atom res2 = [])->
  
    path_split stm1 res1 ->
    path_split stm2 res2 ->
    path_split (Sloop (LINull) stm1 stm2)
      ({|
        pre := pre res1 ++ atoms_conn_pres (normal_atom res1) (pre res2) ++ atoms_conn_pres (continue_atom res1) (pre res2);
        paths := paths res1 ++ paths res2 ++ posts_conn_pres (normal_post res1) (pre res2) ++ posts_conn_pres (continue_post res1) (pre res2) ++
                posts_conn_pres (normal_post res2) (pre res1) ++ (posts_conn_pres (posts_conn_atoms (normal_post res1) (normal_atom res2)) (pre res1))
                ++ (posts_conn_pres (posts_conn_atoms (continue_post res1) (normal_atom res2)) (pre res1))
                ++ (posts_conn_pres (posts_conn_atoms (normal_post res2) (normal_atom res1)) (pre res2))
                ++ (posts_conn_pres (posts_conn_atoms (normal_post res2) (continue_atom res1)) (pre res2))
                ;
        normal_post := (break_post res1) ++ (break_post res2) ++ (posts_conn_atoms (normal_post res1) (break_atom res2));
        continue_post := nil;
        break_post := nil;
        return_post := (return_post res1) ++ (return_post res2) ;
        normal_atom := nil;
        return_atom := return_atom res1 ++ atoms_conn_returns (normal_atom res1) (return_atom res2)
                      ++ atoms_conn_returns (continue_atom res1) (return_atom res2);
        break_atom := break_atom res1 ++ atoms_conn_atoms (normal_atom res1) (break_atom res2)
                      ++ atoms_conn_atoms (continue_atom res1) (break_atom res2)
                      ;
        continue_atom := continue_atom res1;
        |}) 
      
      
      .


(* | Split_loop_single: forall inv c1 c2 res1 res2 
  (Econt_atom: continue_atom res2 = [])
  (Econt_post: continue_post res2 = [])
  (Ebasic_normal1: all_basic (normal_post res1)= true)
  (Ebasic_continue1: all_basic (continue_post res1)= true)
  (Ebasic_pre2: all_basic (pre res2)= true),
    path_split c1 res1 ->
    path_split c2 res2 ->
    path_split (Sloop (LISingle inv) c1 c2) {|
      pre := [(Basic_partial inv,nil)];
      paths := 
        posts_conn_pres [(Basic_partial inv, nil)] (pre res1) ++
        posts_conn_pres [(Basic_partial inv, nil)]
          (atoms_conn_pres (normal_atom res1) (pre res2)) ++
        posts_conn_pres [(Basic_partial inv, nil)]
          (atoms_conn_pres (normal_atom res1)
            (atoms_conn_pres (normal_atom res2)
              [(Basic_partial inv, nil)])) ++
        posts_conn_pres [(Basic_partial inv, nil)]
          (atoms_conn_pres (continue_atom res1)
              (atoms_conn_pres (normal_atom res2)
                [(Basic_partial inv, nil)])) ++
        posts_conn_pres [(Basic_partial inv, nil)]
          (atoms_conn_pres (continue_atom res1) (pre res2)) ++
        paths res1 ++ paths res2 ++
        posts_conn_pres (normal_post res1) (pre res2) ++
        pack_assert_into_post inv 
          (posts_conn_atoms (normal_post res1) (normal_atom res2)) ++
        posts_conn_pres (continue_post res1) (pre res2) ++
        pack_assert_into_post inv
          (posts_conn_atoms (continue_post res1) (normal_atom res2)) ++
        pack_assert_into_posts inv (normal_post res2);
      normal_post :=
        break_post res1 ++ break_post res2 ++
        posts_conn_atoms [(Basic_partial inv, nil)] (break_atom res1) ++
        posts_conn_atoms [(Basic_partial inv, nil)]
          (atoms_conn_atoms (normal_atom res1) (break_atom res2)) ++
        posts_conn_atoms [(Basic_partial inv, nil)]
          (atoms_conn_atoms (continue_atom res1) (break_atom res2)) ++
        posts_conn_atoms (normal_post res1) (break_atom res2) ++
        posts_conn_atoms (continue_post res1) (break_atom res2);
      continue_post := nil;
      break_post := nil;
      return_post :=
        (return_post res1) ++ (return_post res2) ++
        posts_conn_returns [(Basic_partial inv, nil)] (return_atom res1) ++
        posts_conn_returns [(Basic_partial inv, nil)]
          (atoms_conn_returns (normal_atom res1) (return_atom res2)) ++
        posts_conn_returns [(Basic_partial inv, nil)]
          (atoms_conn_returns (continue_atom res1) (return_atom res2)) ++
        posts_conn_returns (normal_post res1) (return_atom res2) ++
        posts_conn_returns (continue_post res1) (return_atom res2) ;
      normal_atom := nil;
      break_atom := nil;
      continue_atom := nil;
      return_atom := nil
          (* no continue condition in c2 *)
    |}. *)

Fixpoint to_Clight  (a: atom_statement) : Clight.statement :=
match a with
| Sskip => Clight.Sskip
| Sassign e1 e2 => Clight.Sassign e1 e2
| Sset id e => Clight.Sset id e
| Scall id e elis => Clight.Scall id e elis
end.

Section Soundness.

Context {CS: compspecs} {Espec: OracleKind} (Delta: tycontext).


Axiom conj_rule : forall  P Q c Q1 Q2 ,
  @semax CS Espec Delta P c (overridePost Q1 Q) ->
  @semax CS Espec Delta P c (overridePost Q2 Q) ->
  @semax CS Espec Delta P c (overridePost (andp Q1 Q2) Q).


Axiom bupd_tc_expr_cong: forall a, (|==> |> FF || tc_expr Delta a) 
                                  |-- tc_expr Delta a.

Axiom bupd_bool_type_cong: forall a, 
    (|==> |> FF || !! (bool_type (typeof a) = true))
    |-- !! (bool_type (typeof a) = true).


Definition split_atom_to_statement (x : (expr + atom_statement)):=
  match x with
  | inl e => (Clight.Sifthenelse e Clight.Sskip Clight.Sbreak)
  | inr s => to_Clight s
  end.


Fixpoint path_to_statement (p:path):  Clight.statement :=
  match p with
  | nil => Clight.Sskip
  | inl e :: p' => Clight.Ssequence 
              (Clight.Sifthenelse e Clight.Sskip Clight.Sbreak) 
              (path_to_statement p')
  | inr s :: p' => Clight.Ssequence
              (to_Clight s) (path_to_statement p')
  end.

Fixpoint path_to_statement'  (p:path):  Clight.statement :=
    fold_Ssequence (map split_atom_to_statement p).


Lemma path_to_statement_app: forall P Q l1 l2,
  semax Delta P (Clight.Ssequence (path_to_statement l1)
    (path_to_statement l2)) Q <->
    semax Delta P (path_to_statement (l1++l2)) Q.
Proof.
  intros. generalize dependent P.
  generalize dependent Q.
  induction l1.
  + simpl. intros;split;intros.
    - apply semax_skip_seq. apply H.
    - apply semax_skip_seq in H. apply H.
  + intros. destruct a; simpl in *.
    { split;intro.
      - apply seq_assoc in H.
        apply semax_seq_inv in H.
        destruct H as [Q0 [E1 E2]].
        eapply semax_seq. apply E1. apply IHl1. auto.
      - apply seq_assoc. apply semax_seq_inv in H.
        destruct H as [Q0 [E1 E2]].
        eapply semax_seq. apply E1. apply IHl1. auto.
    }
    {
      split;intro.
      - apply seq_assoc in H.
        apply semax_seq_inv in H.
        destruct H as [Q0 [E1 E2]].
        eapply semax_seq. apply E1. apply IHl1. auto.
      - apply seq_assoc. apply semax_seq_inv in H.
        destruct H as [Q0 [E1 E2]].
        eapply semax_seq. apply E1. apply IHl1. auto.
    }
Qed.

Inductive extract_exp_from_path (X:Type): 
  (X -> split_assert) -> (X -> split_assert) -> Prop :=
(* extract the first EX out from pre condition *)
| extract_exp_from_path_basic: forall (pre' post': X -> assert),
    extract_exp_from_path X
      (fun x:X => Basic_assert (exp pre') (post' x))
      (fun x:X => Basic_assert (pre' x) (post' x))
| extract_exp_from_path_given: forall Y (HY:Non_empty_Type Y) 
    (ass ass_extracted: Y -> X -> split_assert),
    (forall y:Y, extract_exp_from_path X
         (ass y) (ass_extracted y)) ->
    extract_exp_from_path X
      (fun x:X => (Given_assert Y HY (fun y:Y => ass y x)))
      (fun x:X => (Given_assert Y HY (fun y:Y => ass_extracted y x))).


Inductive path_to_semax : path_statement -> Prop :=
| path_to_semax_given: forall X (HX:Non_empty_Type X)
    (path_ass path_ass': X -> split_assert) path,
    extract_exp_from_path X path_ass path_ass' ->
    (forall x:X, path_to_semax (path_ass' x, path)) ->
    path_to_semax (Given_assert X HX path_ass', path)
| path_to_semax_basic: forall pre path post ,
    @semax CS Espec Delta pre (path_to_statement path)
    {| RA_normal := post;
       RA_break := FALSE;
       RA_continue := FALSE;
       RA_return := fun _ => FALSE|} ->
    path_to_semax (Basic_assert pre post, path)
| path_to_semax_binded: forall X (HX:Non_empty_Type X)  ass' path, 
    (forall x:X, path_to_semax (ass' x, path)) ->
    path_to_semax (Binded_assert X HX ass', path)
.

Inductive add_post_to_semax (post: assert):
  partial_path_statement -> Prop :=
| add_post_to_semax_basic: forall pre path,
    @semax CS Espec Delta pre (path_to_statement path)
    {| RA_normal := post;
      RA_break := FALSE;
      RA_continue := FALSE;
      RA_return := fun _ => FALSE|} ->
      add_post_to_semax post (Basic_partial pre, path)
| add_post_to_semax_binded: forall X (HX:Non_empty_Type X)  pre' path,
    (forall x:X, add_post_to_semax post (pre' x, path)) ->
    add_post_to_semax post (Binded_partial X HX pre', path)
.

Inductive add_return_to_semax (post: option val -> assert):
  return_post_statement -> Prop :=
| add_return_to_semax_basic: forall pre path ret_val,
    @semax CS Espec Delta pre (Clight.Ssequence 
        (path_to_statement path) (Clight.Sreturn ret_val))
    {| RA_normal := FALSE;
      RA_break := FALSE;
      RA_continue := FALSE;
      RA_return := post|} ->
      add_return_to_semax post (Basic_partial pre, path, ret_val)
| add_return_to_semax_binded: forall X(HX:Non_empty_Type X)  pre' path ret_val,
    (forall x:X, add_return_to_semax post (pre' x, path, ret_val)) ->
    add_return_to_semax post (Binded_partial X HX pre', path, ret_val)
.

Inductive add_pre_to_semax (pre: assert):
  partial_path_statement -> Prop :=
| add_pre_to_semax_basic: forall post path,
    @semax CS Espec Delta pre (path_to_statement path)
    {| RA_normal := post;
      RA_break := FALSE;
      RA_continue := FALSE;
      RA_return := fun _ => FALSE|} ->
    add_pre_to_semax pre (Basic_partial post, path)
| add_pre_to_semax_binded: forall X (HX:Non_empty_Type X) post' path,
    (forall x:X, add_pre_to_semax pre (post' x, path)) ->
    add_pre_to_semax pre (Binded_partial X (HX:Non_empty_Type X)  post', path)
.

Inductive atom_to_semax (pre:assert)  (post:assert) : path -> Prop :=
| atom_to_semax_intro: forall path,
    @semax CS Espec Delta pre (path_to_statement path)
    {| RA_normal := post;
       RA_break := FALSE;
       RA_continue := FALSE;
       RA_return := fun _ => FALSE|} ->
    atom_to_semax pre post path.

Inductive atom_return_to_semax (pre:assert)  (post: option val -> assert) :
  path * option expr -> Prop :=
| atom_return_to_semax_intro: forall path ret_val,
    @semax CS Espec Delta pre (Clight.Ssequence 
      (path_to_statement path) (Clight.Sreturn ret_val))
    {| RA_normal := FALSE;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := post|} ->
    atom_return_to_semax pre post (path, ret_val).


Definition split_Semax (P: assert) (Q: ret_assert) (res:split_result) :=
  Forall (add_pre_to_semax P) (pre res)
  /\ Forall path_to_semax (paths res)
  /\ Forall (add_post_to_semax (RA_normal Q)) (normal_post res)
  /\ Forall (add_post_to_semax (RA_break Q)) (break_post res)
  /\ Forall (add_post_to_semax (RA_continue Q)) (continue_post res)
  /\ Forall (add_return_to_semax (RA_return Q)) (return_post res)
  /\ Forall (atom_to_semax P (RA_normal Q)) (normal_atom res)
  /\ Forall (atom_to_semax P (RA_break Q)) (break_atom res)
  /\ Forall (atom_to_semax P (RA_continue Q)) (continue_atom res)
  /\ Forall (atom_return_to_semax P (RA_return Q)) (return_atom res).

Lemma add_pre_to_semax_inv: forall X (HX:Non_empty_Type X)  P pre0 pre',
  Forall (add_pre_to_semax P) pre0 ->
  bind_partial_add X HX pre0 pre' ->
  forall x, Forall (add_pre_to_semax P) (pre' x).
Proof.
  intros.
  induction H0.
    - constructor.
    - inv H. constructor.
      * inv H3. apply inj_pair2 in H2;subst. auto.
      * apply IHbind_partial_add. auto.
Qed.

Lemma add_post_to_semax_inv: forall X (HX:Non_empty_Type X)  Q post post',
  Forall (add_post_to_semax Q) post ->
  bind_partial_add X HX post post' ->
  forall x, Forall (add_post_to_semax Q) (post' x).
Proof.
  intros.
  induction H0.
    - constructor.
    - inv H. constructor.
      * inv H3. apply inj_pair2 in H2;subst. auto.
      * apply IHbind_partial_add. auto.
Qed.

Lemma add_return_to_semax_inv: forall X (HX:Non_empty_Type X) Q post post',
  Forall (add_return_to_semax Q) post ->
  bind_return_add X HX post post' ->
  forall x, Forall (add_return_to_semax Q) (post' x).
Proof.
  intros.
  induction H0.
    - constructor.
    - inv H. constructor.
      * inv H3. apply inj_pair2 in H2;subst. auto.
      * apply IHbind_return_add. auto.
Qed.

Lemma path_to_semax_inv: forall X (HX:Non_empty_Type X) path path',
  Forall path_to_semax path ->
  bind_path_add X HX path path' ->
  forall x, Forall path_to_semax (path' x).
Proof.
  intros.
  induction H0.
  - constructor.
  - inv H. constructor.
    * inv H3. apply inj_pair2 in H2;subst. auto.
    * apply IHbind_path_add. auto.
Qed.

Lemma bind_result_add_inv: forall X (HX:Non_empty_Type X)  P Q res res',
  split_Semax P Q res ->
  bind_result_add X HX res res' -> 
  forall x:X, split_Semax P Q (res' x).
Proof.
  intros.
  inv H0.
  destruct H as [? [? [? [? [? [? [? [? [? ?]]]]]]]]];simpl in *.
  repeat split;simpl;auto.
  + eapply add_pre_to_semax_inv with (HX:=HX). apply H. auto. 
  + eapply path_to_semax_inv with (HX:=HX). apply H0. auto.
  + eapply add_post_to_semax_inv  with (HX:=HX). apply H7. auto. 
  + eapply add_post_to_semax_inv with (HX:=HX). apply H8. auto. 
  + eapply add_post_to_semax_inv with (HX:=HX). apply H9. auto. 
  + eapply add_return_to_semax_inv with (HX:=HX). apply H10. auto.
Qed.

Lemma add_pre_to_semax_derives: forall P Q (x:partial_path_statement),
  derives Q P ->
  add_pre_to_semax P x ->
  add_pre_to_semax Q x.
Proof.
  intros. destruct x as [post path].
  induction post.
  + constructor. inv H0.
    eapply semax_pre0.
    apply H. auto.
  + constructor. inv H0.
    apply inj_pair2 in H4.
    subst. auto.
Qed.

Lemma add_post_to_semax_derives: forall P Q (x:partial_path_statement),
  ENTAIL Delta, Q |-- P ->
  add_post_to_semax Q x ->
  add_post_to_semax P x.
Proof.
  intros. destruct x as [pre path].
  induction pre.
  + constructor. inv H0.
    eapply semax_post;[..|apply H2].
    - unfold RA_normal. apply H.
    - unfold RA_break. apply ENTAIL_refl. 
    - unfold RA_continue.  apply ENTAIL_refl. 
    - intros. unfold RA_return. apply ENTAIL_refl.
  + constructor. inv H0.
    apply inj_pair2 in H4.
    subst. auto.
Qed.



Lemma atom_to_semax_derives: forall P1 P2 Q1 Q2 a,
  P2 |-- P1 ->
  ENTAIL Delta, Q1 |-- Q2 ->
  atom_to_semax P1 Q1 a ->
  atom_to_semax P2 Q2 a.
Proof.
  intros.
  constructor.
  inv H1.
  eapply semax_pre0;[apply H|].
  eapply semax_post;[..|apply H2].
  - unfold RA_normal. apply H0.
  - unfold RA_break. apply ENTAIL_refl. 
  - unfold RA_continue.  apply ENTAIL_refl. 
  - intros. unfold RA_return. apply ENTAIL_refl.
Qed.


Lemma atom_return_to_semax_derives: forall P1 P2 Q1 Q2 a,
  P2 |-- P1 ->
  (forall v, ENTAIL Delta, Q1 v  |-- Q2 v ) ->
  atom_return_to_semax P1 Q1 a ->
  atom_return_to_semax P2 Q2 a.
Proof.
  intros. destruct a as [p r].
  constructor.
  inv H1.
  eapply semax_pre0;[apply H|].
  eapply semax_post;[..|apply H3].
  - unfold RA_normal. apply ENTAIL_refl. 
  - unfold RA_break. apply ENTAIL_refl. 
  - unfold RA_continue.  apply ENTAIL_refl. 
  - intros. unfold RA_return. apply H0.
Qed.


Lemma add_pre_to_semax_sem: forall (x:partial_path_statement),
 (add_pre_to_semax
        (EX Q : assert,
          !! (add_pre_to_semax Q x) && Q)) 
      x.
Proof.
  intros. destruct x as [post path].
  induction post.
  - constructor.
    Intros Q.
    apply semax_extract_prop.
    intros. inv H. auto.
  - constructor.
    intros x.
    specialize (H x).
    eapply add_pre_to_semax_derives;[|apply H].
    Intros Q. Exists Q.
    apply andp_right.
    + apply prop_right. inv H0. apply inj_pair2 in H3. subst.
      auto.
    + apply derives_refl.
Qed.


Lemma add_post_to_semax_reverse: forall post atom R,
  add_post_to_semax R (post_conn_atom post atom) ->
  add_post_to_semax (EX Q, Q && !! ( atom_to_semax Q R atom)) post.
Proof.
  intros. destruct post as [post path].
  induction post.
  - simpl in H.
    inv H.
    apply path_to_statement_app in H1.
    apply semax_seq_inv in H1.
    destruct H1 as [Q [? ?]].
    eapply add_post_to_semax_derives.
    2: { constructor.
         apply H. }
    Exists Q.
    apply andp_right.
    + apply ENTAIL_refl.
    + apply prop_right.
      constructor. auto.
  - constructor. intros.
    apply H0. inv H. apply inj_pair2 in H3. subst. simpl. auto.
Qed.

Lemma path_conn_to_semax_reverse_simple: forall pre a1,
  path_to_semax (post_conn_bind_pre pre [] a1) ->
   add_pre_to_semax a1 pre.
Proof.
  intros.
  destruct pre0 as [a2 p2]. induction a2.
  - inv H. constructor. auto.
  - inv H. apply inj_pair2 in H2. subst.
    constructor. intros. apply H0. simpl. auto.
Qed.
(*
Lemma split_path_to_semax_reverse_group:
forall post pres, pres <> nil ->
 Forall path_to_semax
         (post_conn_pres post pres) ->
  add_post_to_semax (
    EX Q, Q &&
    !!(Forall (add_pre_to_semax Q) pres)
    ) post.

*)



Fixpoint noreturn s :=
 match s with
 | Clight.Ssequence s1 s2 => if noreturn s1 then noreturn s2 else false
 | Clight.Sifthenelse _ s1 s2 => if noreturn s1 then noreturn s2 else false
 | Clight.Sloop s1 s2 => if noreturn s1 then noreturn s2 else false
 | Clight.Sswitch _ sl => noreturn_ls sl
 | Clight.Sgoto _ => false
 | Clight.Sreturn _ => false
 | Clight.Slabel _ s => noreturn s
 | _ => true
end
with noreturn_ls sl :=
 match sl with Clight.LSnil => true | Clight.LScons _ s sl' => if noreturn s then noreturn_ls sl' else false
 end.


Lemma noreturn_ls_spec: forall sl, noreturn_ls sl = true -> noreturn (seq_of_labeled_statement sl) = true.
Proof.
  intros.
  induction sl.
  + reflexivity.
  + simpl in *.
    destruct (noreturn s); [| inv H].
    auto.
Qed.

Lemma noreturn_ls_spec': forall sl n, noreturn_ls sl = true -> noreturn (seq_of_labeled_statement (select_switch n sl)) = true.
Proof.
  intros.
  apply noreturn_ls_spec in H.
  unfold select_switch.
  destruct (select_switch_case n sl) eqn:?Hs.
  + induction sl.
    - inv Hs.
    - simpl in Hs.
      destruct o as [c|]; [destruct (zeq c n) |].
      * subst c; inv Hs.
        apply H.
      * change (noreturn s && noreturn (seq_of_labeled_statement sl) = true)%bool in H.
        rewrite andb_true_iff in H.
        apply IHsl; auto.
        tauto.
      * change (noreturn s && noreturn (seq_of_labeled_statement sl) = true)%bool in H.
        rewrite andb_true_iff in H.
        apply IHsl; auto.
        tauto.
  + induction sl.
    - reflexivity.
    - simpl in Hs |- *.
      destruct o.
      * change (noreturn s && noreturn (seq_of_labeled_statement sl) = true)%bool in H.
        rewrite andb_true_iff in H.
        apply IHsl; [tauto |].
        if_tac in Hs; [inv Hs | auto].
      * exact H.
Qed. 

Lemma semax_noreturn_inv:
  forall Pre s Post Post',
    noreturn s = true ->
    RA_normal Post = RA_normal Post' ->
    RA_break Post = RA_break Post' ->
    RA_continue Post = RA_continue Post' ->
    @semax CS Espec Delta Pre s Post -> @semax CS Espec Delta Pre s Post'.
Proof.
  intros.
  revert Post' H0 H1 H2.
  induction H3; intros.
  + change (noreturn c && noreturn d = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H) _ H0 H1 H2).
    specialize (IHsemax2 (proj2 H) _ H0 H1 H2).
    eapply SeparationLogicAsLogic.AuxDefs.semax_ifthenelse;auto.
  + change (noreturn h && noreturn t = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H)).
    specialize (IHsemax2 (proj2 H) _ H0 H1 H2).
    eapply SeparationLogicAsLogic.AuxDefs.semax_seq; [| eauto].
    apply IHsemax1; destruct Post', R; auto.
  + rewrite H1.
    apply SeparationLogicAsLogic.AuxDefs.semax_break.
  + rewrite H2.
    apply SeparationLogicAsLogic.AuxDefs.semax_continue.
  + simpl in H. change (noreturn body && noreturn incr = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H) (loop1_ret_assert Q' Post')).
    specialize (IHsemax2 (proj2 H)  (loop2_ret_assert Q Post')).
    eapply SeparationLogicAsLogic.AuxDefs.semax_loop with (Q'0:=Q').
    - destruct Post', R.
      unfold loop1_ret_assert in H3_.
      simpl in *. subst. apply IHsemax1;auto.
    - destruct Post', R.
      simpl in *. subst. apply IHsemax2;auto.
  + apply SeparationLogicAsLogic.AuxDefs.semax_switch; auto.
    intros n; specialize (H2 n).
    simpl in H.
    apply (noreturn_ls_spec' _ (Int.unsigned n)) in H.
    specialize (H2 H).
    apply H2; destruct Post', R; simpl; auto.
  + eapply semax_post with (normal_ret_assert R);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply SeparationLogicAsLogic.AuxDefs.semax_call_backward.
  + inv H.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply SeparationLogicAsLogic.AuxDefs.semax_set_ptr_compare_load_cast_load_backward.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply SeparationLogicAsLogic.AuxDefs.semax_store_backward.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply SeparationLogicAsLogic.AuxDefs.semax_skip.
  + apply SeparationLogicAsLogic.AuxDefs.semax_builtin.
  + specialize (IHsemax H _ H0 H1 H2).
    apply SeparationLogicAsLogic.AuxDefs.semax_label; auto.
  + apply SeparationLogicAsLogic.AuxDefs.semax_goto.
  + apply (SeparationLogicAsLogic.AuxDefs.semax_conseq _ P' (Build_ret_assert (RA_normal R') (RA_break R') (RA_continue R') (RA_return Post'))).
    - exact H0.
    - rewrite <- H6; exact H1.
    - rewrite <- H7; exact H2.
    - rewrite <- H8; exact H3.
    - intros. apply derives_full_refl.
    - apply IHsemax; auto.
Qed.

Lemma nocontinue_split_result: forall c, nocontinue (path_to_statement c) = true.
Proof.
  intros.
  induction c.
  + simpl.
    auto.
  + destruct a.
    - simpl. auto.
    - simpl.
      destruct a; auto.
Qed.

Lemma noreturn_split_result: forall c, noreturn (path_to_statement c) = true.
Proof.
  intros.
  induction c.
  + simpl.
    auto.
  + destruct a.
    - simpl. auto.
    - simpl.
      destruct a; auto.
Qed.



Lemma add_return_to_semax_reverse: forall post ret_atom ret_val R,
  add_return_to_semax R (post_conn_return post ret_atom ret_val) ->
  add_post_to_semax (EX Q, Q && !! ( atom_return_to_semax Q R (ret_atom, ret_val))) post.
Proof.
  intros. destruct post as [post path].
  induction post.
  - simpl in H.
    inv H.
    apply semax_seq_inv in H1.
    destruct H1 as [Qret [H1 E2]].
    apply path_to_statement_app in H1.
    apply semax_seq_inv' in H1. unfold overridePost in H1.
    eapply add_post_to_semax_derives with (Q:=
    (EX Q : environ -> mpred,
                       !! DeepEmbeddedDef.semax Delta Q
                            (path_to_statement ret_atom)
                            {|
                            RA_normal := Qret;
                            RA_break := FALSE;
                            RA_continue := FALSE;
                            RA_return := R |} && Q)%assert).
    { Intros Q. Exists Q. apply andp_right.
      apply ENTAIL_refl. apply prop_right. constructor.
      eapply semax_seq. apply H.
      apply E2.
    }
    { constructor.
      eapply semax_noreturn_inv in H1;[apply H1|..].
      + apply noreturn_split_result.
      + reflexivity.
      + reflexivity.
      + reflexivity.
    }
  - constructor. intros.
    apply H0. inv H. apply inj_pair2 in H3. subst. simpl. auto.
Qed.
  

Lemma add_post_to_semax_conj_rule: forall Q1 Q2 post,
  add_post_to_semax Q1 post ->
  add_post_to_semax Q2 post ->
  add_post_to_semax (Q1 && Q2) post.
Proof.
  intros. destruct post as [post path].
  induction post.
  - constructor. inv H. inv H0.
    eapply semax_post.
    5: { eapply conj_rule with (Q1:=Q1) (Q2:=Q2)
          (Q:= {|
            RA_normal := Q2;
            RA_break := FALSE;
            RA_continue := FALSE;
            RA_return := fun _ : option val => FALSE |}).
        + apply H2.
        + apply H1.
    }
    { apply andp_left2. apply derives_refl. }
    { apply ENTAIL_refl. }
    { apply ENTAIL_refl. }
    { intros. apply ENTAIL_refl. }
  - constructor. intros. inv H. apply inj_pair2 in H4. subst.
    inv H0. apply inj_pair2 in H4. subst.
    apply H1;auto.
Qed.

Lemma atom_to_semax_conj_rule: forall P Q1 Q2 atom,
  atom_to_semax P Q1 atom ->
  atom_to_semax P Q2 atom ->
  atom_to_semax P (Q1 && Q2) atom.
Proof.
  intros.
  constructor.
  inv H. inv H0.
  eapply conj_rule with (Q1:=Q1) (Q2:=Q2)
          (Q:= {|
            RA_normal := Q2;
            RA_break := FALSE;
            RA_continue := FALSE;
            RA_return := fun _ : option val => FALSE |});auto.
Qed.

Lemma add_post_to_semax_reverse_group:
forall post atoms R, 
  Forall (add_post_to_semax R)
      (map (post_conn_atom post) atoms) -> atoms <> nil ->
  add_post_to_semax (
    EX Q, Q &&
    !!(Forall (atom_to_semax Q R) atoms)
  ) post.
Proof.
  intros. rename H into H0, H0 into H.
  destruct atoms.
  - exfalso. apply H. auto.
  - induction atoms.
    + eapply add_post_to_semax_derives.
      2:{ apply add_post_to_semax_reverse.
          eapply Forall_forall in H0. apply H0. simpl.
          left. reflexivity. }
      { Intros Q. Exists Q. apply andp_right.
        + apply ENTAIL_refl.
        + apply prop_right. auto. }
    + inv H0. inv H4. assert (p::atoms<>[]) as E1. { intros C. inv C. }
      assert (Forall (add_post_to_semax R)
      (map (post_conn_atom post) (p :: atoms))) as E2 by
      (constructor;auto).
      specialize (IHatoms E2 E1).
      apply add_post_to_semax_reverse in H2.
      eapply add_post_to_semax_derives.
      2:{ eapply add_post_to_semax_conj_rule.
          apply H2. apply IHatoms.  
      }
      { Intros Q1. Intros Q2.
        Exists (Q1 && Q2). apply andp_right.
        + apply ENTAIL_refl.
        + apply prop_right. constructor.
          - inv H1.
            eapply atom_to_semax_derives;[..|apply H7].
            { apply andp_left2. apply derives_refl. }
            { apply ENTAIL_refl. }
          - constructor.
            eapply atom_to_semax_derives;[..|apply H0].
            { apply andp_left1. apply derives_refl. }
            { apply ENTAIL_refl. }
            apply Forall_forall. intros.
            eapply atom_to_semax_derives.
            3: { eapply Forall_forall in H1. apply H1. right. auto. }
            { apply andp_left2. apply derives_refl. }
            { apply ENTAIL_refl. }        
      }
Qed.

Lemma atom_return_to_semax_derives_pre: forall p P1 P2 Q,
    P1 |-- P2 ->
    atom_return_to_semax P2 Q p ->
    atom_return_to_semax P1 Q p.
Proof.
  intros.
  destruct p.
  constructor.
  inv H0.
  eapply semax_pre.
  + simpl. intros. apply andp_left2. apply H.
  + apply H2.
Qed.


Lemma add_return_to_semax_reverse_group:
forall post ret_atoms R, 
  Forall (add_return_to_semax R)
  (map (
    fun ret_atom => post_conn_return post (fst ret_atom) (snd ret_atom)) ret_atoms)
   -> ret_atoms <> nil ->
  add_post_to_semax (
    EX Q, Q &&
    !!(Forall (atom_return_to_semax Q R) ret_atoms)
  ) post.
Proof.
  intros. rename H into H0, H0 into H.
  destruct ret_atoms.
  - exfalso. apply H. auto.
  - induction ret_atoms.
    + eapply add_post_to_semax_derives.
      2:{ apply add_return_to_semax_reverse. simpl in H0.
          inv H0. apply H3. }
      { Intros Q. Exists Q. apply andp_right.
        + apply ENTAIL_refl.
        + apply prop_right. constructor. destruct p. auto. constructor. }
    + inv H0. inv H4. assert (p::ret_atoms<>[]) as E1. { intros C. inv C. }
      assert (Forall (add_return_to_semax R)
      (map (fun ret_atom : path * option expr =>
              post_conn_return post (fst ret_atom) (snd ret_atom))
           (p :: ret_atoms))) as E2 by
      (constructor;auto).
      specialize (IHret_atoms E2 E1).
      apply add_return_to_semax_reverse in H2.
      eapply add_post_to_semax_derives.
      2:{ eapply add_post_to_semax_conj_rule.
          apply H2. apply IHret_atoms.  
      }
      { Intros Q1. Intros Q2.
        Exists (Q1 && Q2). apply andp_right.
        + apply ENTAIL_refl.
        + apply prop_right. constructor.
          - inv H1.
            eapply atom_return_to_semax_derives_pre;[..|apply H7].
            { apply andp_left2. apply derives_refl. }
          - constructor. rewrite <- surjective_pairing in H0.
            eapply atom_return_to_semax_derives_pre;[..|apply H0].
            { apply andp_left1. apply derives_refl. }
            apply Forall_forall. intros.
            eapply  atom_return_to_semax_derives_pre.
            2: { eapply Forall_forall in H1. apply H1. right. auto. }
            { apply andp_left2. apply derives_refl. }
      }
Qed.


Lemma atoms_conn_pres_nil: forall atoms pres,
  atoms_conn_pres atoms pres = [] ->
  atoms = [] \/ pres = [].
Proof.
  induction atoms.
  + intros. simpl in H. auto.
  + intros. right. destruct pres;auto.
    simpl in *. inversion H.
Qed.

Lemma atoms_conn_atoms_nil: forall atoms1 atoms2,
  atoms_conn_atoms atoms1 atoms2 = []
  -> atoms1 = [] \/ atoms2 = [].
Proof.
  intros.
  destruct atoms1;auto.
  right. destruct atoms2;auto.
  inversion H.
Qed.

Lemma atoms_conn_returns_nil: forall atoms1 rets2,
  atoms_conn_returns atoms1 rets2 = []
  -> atoms1 = [] \/ rets2 = [].
Proof.
  intros.
  destruct atoms1;auto.
  right. destruct rets2;auto.
  inversion H.
Qed.


Lemma posts_conn_pre_app: forall posts1 posts2 pre,
    posts_conn_pre (posts1 ++ posts2) pre =
    posts_conn_pre posts1 pre ++ posts_conn_pre posts2 pre.
Proof.
  intros.
  induction posts1.
  - rewrite app_nil_l. simpl. reflexivity.
  - rewrite <- app_comm_cons.
    destruct a as [a1 p1]. destruct pre0 as [a2 p2].
    destruct a1.
    + destruct p1.
      * destruct a2.
        { simpl.  rewrite IHposts1. reflexivity. }
        { simpl.  rewrite IHposts1. reflexivity. }
      * destruct a2.
        { simpl.  rewrite IHposts1. reflexivity. }
        { simpl.  rewrite IHposts1. reflexivity. }
    + destruct a2; simpl.
      { rewrite IHposts1. auto. }
      { apply IHposts1. }
Qed.


Lemma path_conn_to_semax_reverse_group1: forall a1 posts pres,
   In (Basic_partial a1, []) posts -> pres <> [] ->
      Forall path_to_semax
         (posts_conn_pres posts pres)
      -> add_post_to_semax (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Q) pres) (Basic_partial a1, []).
Proof.
  intros.
  destruct pres.
  - exfalso. apply H0. auto.
  - induction pres.
    { constructor.
      simpl in H1. rewrite app_nil_r in H1.
      pose proof proj1 (Forall_forall _ _) H1.
      eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply semax_skip];
        unfold normal_ret_assert.
      + unfold RA_normal, normal_ret_assert. Exists a1. apply andp_right.
        apply derives_refl. apply prop_right. constructor;[|constructor].
        eapply path_conn_to_semax_reverse_simple. apply H2.
        apply in_split in H. destruct H as [posts1 [posts2 H]].
        rewrite H. rewrite posts_conn_pre_app. apply in_or_app. right.
        destruct p as [p2 a2]. destruct p2;simpl;auto.
      + unfold RA_break. apply FF_left.
      + apply FF_left.
      + intros. apply FF_left. }
    { assert (p::pres<>[]) by (intros C;inversion C).
      specialize (IHpres H2).
      assert (Forall path_to_semax (posts_conn_pres posts (p :: pres))).
      { apply Forall_forall. intros. apply (proj1 (Forall_forall _ _) H1).
        apply in_app_or in H3. apply in_or_app. destruct H3;auto. right.
        apply in_or_app. auto. }
      specialize (IHpres H3).
      assert (add_post_to_semax
             (EX Q : assert, Q && !! Forall (add_pre_to_semax Q) [a])
             (Basic_partial a1, [])).
      { constructor.
        eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply semax_skip];
        unfold normal_ret_assert.
        + unfold RA_normal, normal_ret_assert. Exists a1. apply andp_right.
          apply derives_refl. apply prop_right. constructor;[|constructor].
          eapply path_conn_to_semax_reverse_simple.
          apply (proj1 (Forall_forall _ _) H1). apply in_or_app. right.
          apply in_or_app. left.
          apply in_split in H. destruct H as [posts1 [posts2 H]].
          rewrite H. rewrite posts_conn_pre_app. apply in_or_app. right.
          destruct a as [p2 a2]. destruct p2;simpl;auto.
        + unfold RA_break. apply FF_left.
        + apply FF_left.
        + intros. apply FF_left.
      }
      eapply add_post_to_semax_derives.
      2:{ eapply add_post_to_semax_conj_rule.
          apply H4. apply IHpres.  
      }
      { Intros Q1. Intros Q2.
        Exists (Q1 && Q2). apply andp_right.
        + apply ENTAIL_refl.
        + apply prop_right. constructor.
          - inv H6.
            eapply add_pre_to_semax_derives;[..|apply H9].
            { apply andp_left2. apply derives_refl. }
          - constructor.
            { inv H5. eapply add_pre_to_semax_derives;[..|apply H9].
              { apply andp_left1. apply derives_refl. } }
            { inv H6. apply Forall_forall. intros.
              apply (proj1 (Forall_forall _ _) H10) in H6.
              eapply add_pre_to_semax_derives;[..|apply H6].
              { apply andp_left2. apply derives_refl. } }
      }
    }    
Qed.
  


Lemma path_conn_to_semax_reverse_group2: forall a1 p1 posts pres,
   In (Basic_partial a1, p1) posts -> pres <> nil -> all_basic pres = true  ->
      Forall path_to_semax
         (posts_conn_pres posts pres)
      -> add_post_to_semax (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Q) pres) (Basic_partial a1, p1).
Proof.
  intros.
  destruct pres.
  - exfalso. apply H0. auto.
  - destruct p as [a2 p2]. induction pres.
    { constructor.
      simpl in H1. destruct a2; try inversion H1. simpl in H2.
      rewrite app_nil_r in H2.
      pose proof proj1 (Forall_forall _ _) H2.
      specialize (H3 (post_conn_bind_pre (Basic_partial a, p2) p1 a1)).
      simpl in H3.
      assert ( In (Basic_assert a1 a, p1 ++ p2)
                  (posts_conn_pre posts (Basic_partial a, p2))).
      { apply in_split in H. destruct H as [posts1 [posts2 H]].
        rewrite H. rewrite posts_conn_pre_app. apply in_or_app. right.
        destruct p1.
        - simpl. left;auto.
        - simpl. left;auto.
      }
      apply H3 in H4.
      inv H4. apply path_to_statement_app in H6.
      apply semax_seq_inv' in H6. simpl in H6.
      eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply H6];intros;
        try apply derives_refl.
      simpl. intros. Intros Q. Exists Q.
      apply andp_right;[apply derives_refl|apply prop_right].
      constructor;[|constructor]. constructor.
      auto.
    }
    {
      assert (E1: (a2,p2)::pres <> []). { intros C. inv C. }
      assert (E2: all_basic ((a2,p2)::pres)=true).
      { simpl in H1. destruct a2;simpl.
        + destruct a as [a3 p3]. destruct a3;auto. inv H1.
        + inv H1.
      }
      assert (E3: Forall path_to_semax (posts_conn_pres posts ((a2,p2)::pres))).
      { apply Forall_forall. intros.
        apply (proj1 (Forall_forall _ _) H2).
        apply in_app_or in H3. apply in_or_app. destruct H3;auto.
        right. apply in_or_app. right. auto. }
      specialize (IHpres E1 E2 E3);clear E1 E2 E3.
      destruct a as [a3 p3].
      destruct a3.
      2: { destruct a2;try inv H1. }
      assert (E1: path_to_semax (post_conn_bind_pre (Basic_partial a,p3) p1 a1)).
      {
        apply in_split in H. destruct H as [posts1 [posts2 H]].
        rewrite H in H2.
        apply (proj1 (Forall_forall _ _) H2).
        simpl. apply in_or_app. right. apply in_or_app. left.
        rewrite posts_conn_pre_app. apply in_or_app. right.
        simpl. destruct p1;simpl;auto.
      }
      simpl in E1.
      assert (E2: add_post_to_semax (EX Q:assert, Q &&
                        !! (add_pre_to_semax Q)(Basic_partial a, p3))
                                    (Basic_partial a1,p1)).
      { constructor.
        inv E1.
        apply path_to_statement_app in H4.
        apply semax_seq_inv' in H4. simpl in H4.
        eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply H4];intros;
          try apply derives_refl.
        simpl. intros. Intros Q. Exists Q.
        apply andp_right;[apply derives_refl|]. apply prop_right.
        constructor. auto.
      }
      eapply add_post_to_semax_derives.
      2:{ eapply add_post_to_semax_conj_rule.
          apply E2. apply IHpres.  
      }
      { Intros Q1. Intros Q2.
        Exists (Q1 && Q2). apply andp_right.
        + apply ENTAIL_refl.
        + apply prop_right. constructor.
          - inv H4.
            eapply add_pre_to_semax_derives;[..|apply H7].
            { apply andp_left2. apply derives_refl. }
          - constructor.
            { eapply add_pre_to_semax_derives;[..|apply H3].
            { apply andp_left1. apply derives_refl. } }
            { inv H4. apply Forall_forall. intros.
              apply (proj1 (Forall_forall _ _) H8) in H4.
              eapply add_pre_to_semax_derives;[..|apply H4].
              { apply andp_left2. apply derives_refl. } }
      }
    }    
Qed.

Lemma path_conn_to_semax_reverse_group2': forall a1 p1 posts pres,
   In (Basic_partial a1, p1) posts -> 
   all_basic pres = true  ->
   Forall path_to_semax
         (posts_conn_pres posts pres) ->
   pres <> nil -> 
      add_post_to_semax (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Q) pres) (Basic_partial a1, p1).
Proof.
  intros.
  eapply path_conn_to_semax_reverse_group2;[apply H|..];auto.
Qed.

Lemma all_empty_path_sem: forall posts a p,
        all_empty_path posts = true ->
        In (Basic_partial a, p) posts -> p = [].
Proof.
  intros.
  induction posts.
  + inv H0.
  + destruct H0. inv H0.
    simpl in H. destruct p;auto. inv H.
    apply IHposts;auto. simpl in H. destruct a0. destruct p1;auto.
    inv H.
Qed.

Lemma all_empty_atom_sem: forall atoms p,
        all_empty_atom atoms = true ->
        In p atoms -> p = [].
Proof.
  intros.
  induction atoms.
  + inv H0.
  + destruct H0. inv H0.
    simpl in H. destruct p;auto. inv H.
    apply IHatoms;auto. simpl in H. destruct a.  auto.
    inv H.
Qed.

Lemma all_basic_sem: forall posts X a p (HX:Non_empty_Type X),
        all_basic posts = true ->
        In (Binded_partial X HX  a, p) posts -> False.
Proof.
  intros.
  induction posts.
  + inv H. inv H0.
  + destruct H0. inv H0.
    simpl in H.  inv H.
    eapply IHposts;auto. simpl in H.
    destruct a0. destruct p0;auto.
    inv H.
Qed.

Lemma path_conn_to_semax_reverse_group3: forall a1 p1 posts pres,
    In (Basic_partial a1, p1) posts -> pres <> nil ->
    (all_basic pres = false -> all_empty_path posts = true) ->
     Forall path_to_semax
         (posts_conn_pres posts pres)
      -> add_post_to_semax (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Q) pres) (Basic_partial a1, p1).
Proof.
  intros.
  destruct (all_basic pres) eqn:Eb.
  - pose proof (path_conn_to_semax_reverse_group2 _ _ _ _ H H0 Eb). auto.
  - specialize (H1 eq_refl). pose proof all_empty_path_sem _ _ _ H1 H. subst.
    eapply path_conn_to_semax_reverse_group1;auto. apply H. auto.
Qed. 

Lemma path_conn_to_semax_reverse:forall p2 a2 (post:partial_path_statement) ,
path_to_semax (bind_post_conn_pre post p2 a2)-> 
add_post_to_semax (EX Q: assert, Q && !! (add_pre_to_semax Q) (Basic_partial a2,p2)) (post).
Proof.
  intros.
  destruct post as [a1 p1].
  induction a1.
  - constructor. inv H. apply path_to_statement_app in H1. apply semax_seq_inv in H1. destruct H1 as [Q [H1 H2]].
    unfold overridePost in H1. eapply semax_conseq;[..|apply H1]. 
    + apply derives_full_refl.
    + unfold RA_normal. (* Search bupd later derives. *) apply aux1_reduceR. (* Search derives bupd. *) eapply derives_trans.
    2:{apply bupd_intro. }
    1:{ Exists Q. apply andp_right. solve_andp. apply prop_right. constructor. apply H2. }
    + unfold RA_break. apply derives_full_refl.
    + unfold RA_continue. apply derives_full_refl.
    + intros. unfold RA_return. apply derives_full_refl.
  - constructor. intros. apply H0. simpl in H. inv H. apply inj_pair2 in H2. subst.
    simpl. apply H5.
    Qed.

Lemma posts_conn_basic_pre_cons: forall post posts a2 p2,
  posts_conn_pre (post::posts) (Basic_partial a2, p2) =
  (bind_post_conn_pre post p2 a2) :: posts_conn_pre posts (Basic_partial a2, p2).
Proof.
  intros. destruct post as [a1 p1]. destruct a1; simpl; try auto.
  destruct p1;auto.
Qed.

Lemma path_conn_to_semax_reverse_group4: forall post posts pres,
  pres <> []-> In (post) posts ->
   all_basic pres = true -> Forall path_to_semax (posts_conn_pres posts pres)
      -> add_post_to_semax (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Q) pres) (post).
Proof.
  intros.
  destruct pres.
  - exfalso. apply H. auto.
  - induction pres.
  + unfold posts_conn_pres in H2. rewrite flat_map_concat_map in H2.
    simpl in H2. rewrite app_nil_r in H2. apply in_split in H0.
    destruct H0 as [l1 [l2 H0]]. subst posts.
    rewrite posts_conn_pre_app in H2. apply Forall_app in H2.
    destruct H2 as [H2 H3]. destruct p as [a2 p2].
    destruct a2. 2:{ inv H1. } rewrite posts_conn_basic_pre_cons in H3.
    inv H3. eapply add_post_to_semax_derives.
    2:{ apply path_conn_to_semax_reverse. apply H5. }
    Intros Q. Exists Q. apply andp_right; try solve_andp.
    apply prop_right. constructor;auto.
  + Check add_post_to_semax_conj_rule.
    destruct p as [a1 p1], a as [a2 p2]. destruct a1, a2; inv H1.
    apply in_split in H0. destruct H0 as [l1 [l2 H0]].
    eapply add_post_to_semax_derives. 
    2:{ apply add_post_to_semax_conj_rule. 
    ++ apply IHpres.
       - intros c. inv c. 
       - simpl. auto.
       - apply Forall_forall. intros. eapply Forall_forall in H2. apply H2.
         unfold posts_conn_pres in *. rewrite flat_map_concat_map in H1.
         simpl in H3. rewrite flat_map_concat_map. simpl.
         apply in_app_or in H1. destruct H1.
         + apply in_or_app. auto.
         + apply in_or_app. right. apply in_or_app. auto.
    ++ apply path_conn_to_semax_reverse. eapply Forall_forall in H2.
      apply H2. apply in_or_app. right. apply in_or_app. left.
      rewrite H0. rewrite posts_conn_pre_app. apply in_or_app. right.
      rewrite posts_conn_basic_pre_cons. left. reflexivity. }
  { Intros Q1 Q2. Exists (Q1 && Q2). apply andp_right.
    - solve_andp.
    - apply prop_right. apply Forall_forall. intros. 
      destruct H5.
      + eapply add_pre_to_semax_derives. apply andp_left1. apply derives_refl.
        eapply Forall_forall in H1. apply H1.
        left. exact H5.
      + destruct H5. eapply add_pre_to_semax_derives. apply andp_left2. apply derives_refl.
        rewrite H5 in H3. exact H3.
        eapply add_pre_to_semax_derives. apply andp_left1. apply derives_refl.
        eapply Forall_forall in H1. apply H1. right. auto. }
    Qed.

Lemma path_conn_to_semax_reverse_group: forall x posts pres,
    In x posts ->
    (all_basic posts = true /\
     (all_basic pres = false -> all_empty_path posts = true)) ->
     Forall path_to_semax
            (posts_conn_pres posts pres)
            ->
    pres <> nil 
      -> add_post_to_semax (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Q) pres) x.
Proof.
  intros. destruct H0.
  destruct x as [a1 p1]. destruct a1.
  - eapply path_conn_to_semax_reverse_group3;[apply H|..];auto.
  - exfalso. eapply all_basic_sem. apply H0. apply H.
Qed. 

Lemma path_conn_to_semax_reverse_group': forall x pres posts atoms,
    In x posts->
    ((all_basic pres = true) \/
    ( (all_basic(posts) = true)/\
      (all_empty_path posts = true)/\
      (all_empty_atom atoms = true)
    )) ->
    Forall path_to_semax (posts_conn_pres posts pres) ->
    pres <>nil->
    add_post_to_semax (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Q) pres) x.
Proof.
  intros. destruct H0. destruct x as [a1 p1]. (* destruct a1. *)
  2:{ eapply path_conn_to_semax_reverse_group;auto.
      - apply H.
      - destruct H0;auto. split;auto.
        intros. apply H3.
      - auto. }
  1:{ eapply path_conn_to_semax_reverse_group4;auto.
      apply H. auto.
      }  
  Qed.
  
Lemma add_exp_to_atoms_nil: forall a l,  add_exp_to_atoms a l = [] -> l = [].
Proof.
  intros.
  destruct l;auto.
  inv H.
Qed.

Lemma add_exp_to_return_atoms_nil: forall a l,  add_exp_to_return_atoms a l = [] -> l = [].
Proof.
  intros.
  destruct l;auto.
  inv H.
Qed.

Lemma add_exp_to_pres_nil: forall a l,  add_exp_to_pres a l = [] -> l = [].
Proof.
  intros.
  destruct l;auto.
  inv H.
Qed.

Lemma split_not_empty: forall stm res, path_split stm res ->
  ~ (pre res = [] /\ normal_atom res = []
     /\ break_atom res = [] /\ continue_atom res = []
     /\ return_atom res = []).
Proof.
  induction 1.
  + destruct HX as [x ?].  
    inv H. simpl in *. subst.
    intros C; destruct C as [? [? [? [? ?]]]]; subst; simpl in *.
    inv H2. apply H1;auto.
  + intros C; destruct C as [? [? [? [? ?]]]]; subst; simpl in *.
    apply app_eq_nil in H6. destruct H6 as [? ?].
    apply app_eq_nil in H2. destruct H2 as [? ?].
    apply app_eq_nil in H4. destruct H4 as [? ?].
    apply app_eq_nil in H5. destruct H5 as [? ?].
    destruct (classic (normal_atom res1 = [])).
    { apply IHpath_split1;auto. }
    apply atoms_conn_pres_nil in H8. destruct H8;auto.
    apply atoms_conn_atoms_nil in H3. destruct H3;auto.
    apply atoms_conn_atoms_nil in H9. destruct H9;auto.
    apply atoms_conn_atoms_nil in H10. destruct H10;auto.
    apply atoms_conn_returns_nil in H7. destruct H7;auto.
    apply IHpath_split2;auto.
  + intros C.
    inv H;simpl in *;destruct C as [? [? [? [? ?]]]].
    - inv H0.
    - inv H0.
    - inv H.
    - inv H2.
    - inv H1.
    - inv H0.
    - inv H3.
    - inv H0.
  + intros C; destruct C as [? [? [? [? ?]]]]; subst; simpl in *.
    apply app_eq_nil in H1. destruct H1 as [? ?].
    apply app_eq_nil in H2. destruct H2 as [? ?].
    apply app_eq_nil in H3. destruct H3 as [? ?].
    apply app_eq_nil in H4. destruct H4 as [? ?].
    apply app_eq_nil in H5. destruct H5 as [? ?].
    apply add_exp_to_pres_nil in H1.
    apply add_exp_to_pres_nil in H6.
    apply add_exp_to_atoms_nil in H2. apply add_exp_to_atoms_nil in H3.
    apply add_exp_to_atoms_nil in H4. apply add_exp_to_atoms_nil in H8.
    apply add_exp_to_atoms_nil in H7. apply add_exp_to_atoms_nil in H9.
    apply add_exp_to_return_atoms_nil in H5.
    apply add_exp_to_return_atoms_nil in H10.
    rewrite H1, H2, H3, H4, H5 in *.
    apply IHpath_split1;auto.
  + intros C; destruct C as [? [? [? [? ?]]]]; subst; simpl in *. inv H1.
  + auto.
Qed.


Lemma nil_cons {A:Type} {a:A} {b: list A}: a :: b <> [].
Proof. intros C. inv C. Qed.


Lemma atoms_conn_pres_app1: forall atoms1 atoms2 pres,
    atoms_conn_pres (atoms1 ++ atoms2) pres =
    atoms_conn_pres atoms1 pres ++ atoms_conn_pres atoms2 pres.
Proof.
  intros.
  induction atoms1.
  - rewrite app_nil_l. simpl. reflexivity.
  - rewrite <- app_comm_cons.
    simpl.
    rewrite IHatoms1.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma atoms_conn_pres_nil2: forall atoms,
    atoms_conn_pres atoms [] = [].
Proof.
  intros.
  induction atoms;simpl;auto.
Qed.


Lemma atoms_conn_pres_app2: forall pres1 pres2 atoms x,
  In x (atoms_conn_pres atoms (pres1 ++ pres2)) <->
  In x (atoms_conn_pres atoms pres1  ++ atoms_conn_pres atoms pres2).
Proof.
  intros. induction atoms.
  - simpl. tauto.
  - simpl. split;intro.
    + apply in_or_app. apply in_app_or in H.
      destruct H.
      { rewrite map_app in H. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply in_or_app. auto.
      }
      { apply IHatoms in H. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply in_or_app. auto.
      }
    + apply in_or_app. apply in_app_or in H. destruct H.
      { rewrite map_app. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply IHatoms. apply in_or_app. auto.
      }
      {  rewrite map_app. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply IHatoms. apply in_or_app. auto.
      }
Qed.

   


Lemma atom_conn_pres_to_semax_reverse_group1: forall  atoms pres P,
   In [] atoms -> pres <> [] ->
      Forall (add_pre_to_semax P)
         (atoms_conn_pres atoms pres)
      -> atom_to_semax P (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Q) pres) [].
Proof.
  intros. destruct pres.
  - exfalso. apply H0. auto.
  - induction pres.
    { constructor.
      eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply semax_skip];
        intros;try apply FF_left; unfold RA_normal, normal_ret_assert.
      Exists P. apply andp_right;[apply derives_refl|apply prop_right].
      constructor;auto.
      eapply Forall_forall in H1. apply H1.
      apply in_split in H. destruct H as [atoms1 [atoms2 H]].
      rewrite H.
      simpl.
      rewrite atoms_conn_pres_app1.
      apply in_or_app. right.
      simpl. left. unfold atom_conn_pre. destruct p.
      simpl. auto. }
    { assert (p::pres<>[]) by (intros C;inversion C).
      specialize (IHpres H2).
      assert (Forall (add_pre_to_semax P) (atoms_conn_pres atoms (p :: pres))).
      { apply Forall_forall. intros. apply (proj1 (Forall_forall _ _) H1).
        replace (p::pres) with ([p]++pres) in H3 by reflexivity.
        rewrite atoms_conn_pres_app2 in H3.
        apply in_app_or in H3.
        replace (p::a::pres) with([p]++[a]++pres) by reflexivity.
        rewrite atoms_conn_pres_app2. apply in_or_app.
        destruct H3;auto. right.
        apply atoms_conn_pres_app2.
        apply in_or_app. auto. }
      specialize (IHpres H3).
      assert (atom_to_semax
               P (EX Q : assert, Q && !! Forall (add_pre_to_semax Q) [a])
             []).
      { constructor.
        eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply semax_skip];
          unfold normal_ret_assert;intros;try apply FF_left;unfold RA_normal.
        Exists P. apply andp_right.
        apply derives_refl. apply prop_right. constructor;[|constructor].
        apply (proj1 (Forall_forall _ _) H1).
        apply in_split in H. destruct H as [atoms1 [atoms2 H]]. subst atoms.
        rewrite atoms_conn_pres_app1. apply in_or_app. right.
        simpl. unfold atom_conn_pre. destruct a. auto.
      }
      eapply atom_to_semax_derives.
      1:{ apply derives_refl. }
      2:{ eapply atom_to_semax_conj_rule.
          apply H4. apply IHpres.  
      }
      { Intros Q1. Intros Q2.
        Exists (Q1 && Q2). apply andp_right.
        + apply ENTAIL_refl.
        + apply prop_right. constructor.
          - inv H6.
            eapply add_pre_to_semax_derives;[..|apply H9].
            { apply andp_left2. apply derives_refl. }
          - constructor.
            { inv H5. eapply add_pre_to_semax_derives;[..|apply H9].
            { apply andp_left1. apply derives_refl. } }
            { inv H6. apply Forall_forall. intros.
              apply (proj1 (Forall_forall _ _) H10) in H6.
              eapply add_pre_to_semax_derives;[..|apply H6].
              { apply andp_left2. apply derives_refl. } }
      }
    }
Qed.



Lemma atom_conn_pres_to_semax_reverse_group2: forall P p pres atoms,
   In p atoms -> pres <> nil -> all_basic pres = true  ->
      Forall (add_pre_to_semax P)
         (atoms_conn_pres atoms pres)
      -> atom_to_semax P (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Q) pres) p.
Proof.
  intros.
  destruct pres.
  - exfalso. apply H0. auto.
  -  induction pres.
    { constructor. destruct p0 as [a2 p2].
      simpl in H1. destruct a2; try inversion H1.
      pose proof proj1 (Forall_forall _ _) H2.
      specialize (H3 (atom_conn_pre p (Basic_partial a, p2))).
      assert ( In (atom_conn_pre p (Basic_partial a, p2))
         (atoms_conn_pres atoms [(Basic_partial a, p2)])).
      { apply in_split in H. destruct H as [atoms1 [atoms2 H]].
        rewrite H. rewrite atoms_conn_pres_app1. apply in_or_app. right.
        simpl. auto.
      }
      apply H3 in H4. clear H3.
      inv H4. apply path_to_statement_app in H5.
      apply semax_seq_inv' in H5. simpl in H5.
      eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply H5];intros;
        try apply derives_refl.
      simpl. intros. Intros Q. Exists Q.
      apply andp_right;[apply derives_refl|apply prop_right].
      constructor;[|constructor]. constructor.
      auto.
    }
    {
      assert (E1: p0::pres <> []). { intros C. inv C. }
      assert (E2: all_basic (p0::pres)=true).
      { destruct a as [a1 p1].
        destruct p0 as [a2 p2].
        destruct a1,a2;simpl;inv H1;auto.
      }
      assert (E3:Forall (add_pre_to_semax P) (atoms_conn_pres atoms (p0 :: pres))).
      { apply Forall_forall. intros.
        apply (proj1 (Forall_forall _ _) H2).
        replace (p0::pres) with ([p0]++pres) in H3 by reflexivity.
        rewrite atoms_conn_pres_app2 in H3.
        apply in_app_or in H3.
        replace (p0::a::pres) with([p0]++[a]++pres) by reflexivity.
        rewrite atoms_conn_pres_app2. apply in_or_app.
        destruct H3;auto. right.
        apply atoms_conn_pres_app2.
        apply in_or_app. auto.  }
      specialize (IHpres E1 E2 E3);clear E1 E2 E3.
      destruct a as [a3 p3].
      destruct a3.
      2: { destruct p0 as [a2 p2]. destruct a2;try inv H1. }
      assert (E1: add_pre_to_semax P (atom_conn_pre p (Basic_partial a,p3))).
      {
        apply in_split in H. destruct H as [posts1 [posts2 H]].
        rewrite H in H2.
        apply (proj1 (Forall_forall _ _) H2).
        simpl.  rewrite atoms_conn_pres_app1. apply in_or_app.
        right. apply in_or_app. left.
        simpl. auto.
      }
      simpl in E1.
      assert (E2: atom_to_semax P (EX Q:assert, Q &&
                        !! (add_pre_to_semax Q)(Basic_partial a, p3)
                                    ) p).
      { constructor.
        inv E1.
        apply path_to_statement_app in H4.
        apply semax_seq_inv' in H4. simpl in H4.
        eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply H4];intros;
          try apply derives_refl.
        simpl. intros. Intros Q. Exists Q.
        apply andp_right;[apply derives_refl|]. apply prop_right.
        constructor. auto.
      }
      eapply atom_to_semax_derives.
      1:{ apply derives_refl. }
      2:{ eapply atom_to_semax_conj_rule.
          apply E2. apply IHpres.  
      }
      { Intros Q1. Intros Q2.
        Exists (Q1 && Q2). apply andp_right.
        + apply ENTAIL_refl.
        + apply prop_right. constructor.
          - inv H4.
            eapply add_pre_to_semax_derives;[..|apply H7].
            { apply andp_left2. apply derives_refl. }
          - constructor.
            { eapply add_pre_to_semax_derives;[..|apply H3].
            { apply andp_left1. apply derives_refl. } }
            { inv H4. apply Forall_forall. intros.
              apply (proj1 (Forall_forall _ _) H8) in H4.
              eapply add_pre_to_semax_derives;[..|apply H4].
              { apply andp_left2. apply derives_refl. } }
      }
    }    
Qed.

Lemma atom_conn_pres_to_semax_reverse_group2': forall P p pres atoms,
   In p atoms -> all_basic pres = true  ->
      Forall (add_pre_to_semax P)
         (atoms_conn_pres atoms pres) ->
      pres <> nil
      -> atom_to_semax P (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Q) pres) p.
Proof. intros.
  eapply atom_conn_pres_to_semax_reverse_group2.
  apply H. auto. auto. auto.
Qed.

Lemma atom_conn_pres_to_semax_reverse_group3: forall P p atoms pres,
    In p atoms ->
    (all_basic pres = false -> all_empty_atom atoms = true) ->
     Forall (add_pre_to_semax P)
            (atoms_conn_pres atoms pres) ->
      pres <> nil 
      -> atom_to_semax P (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Q) pres) p.
Proof.
  intros.
  destruct (all_basic pres) eqn:Eb.
  - pose proof (atom_conn_pres_to_semax_reverse_group2 P _ _ _ H H2 Eb). auto.
  - specialize (H0 eq_refl). pose proof all_empty_atom_sem _ _ H0 H. subst.
    eapply atom_conn_pres_to_semax_reverse_group1;auto. apply H. auto.
Qed.

Lemma atom_conn_pres_to_semax_reverse_group3': forall P p atoms pres,
    In p atoms ->
    ((all_basic pres = true)   \/ (all_empty_atom atoms = true)) ->
    Forall (add_pre_to_semax P) (atoms_conn_pres atoms pres) ->
      pres <> nil -> 
    atom_to_semax P (EX Q: assert, Q && !! Forall (add_pre_to_semax Q) pres) p.
Proof.
  intros. destruct H0.
  - (*all_basic pres = true*)
    eapply atom_conn_pres_to_semax_reverse_group2';auto. 
    apply H. apply H1. 
  - (*all_empty_atom atoms = true *)
    eapply atom_conn_pres_to_semax_reverse_group3;auto.
    apply H. intros;auto. apply H1.
 Qed. 

Lemma add_return_to_atom_semax_reverse: forall atom ret_atom ret_val P R,
  atom_return_to_semax P R ( atom ++ ret_atom, ret_val) ->
  atom_to_semax P (EX Q, Q && !!
                 ( atom_return_to_semax Q R (ret_atom, ret_val))) atom.
Proof.
  intros.
  inv H.
  apply semax_seq_inv in H1.
  destruct H1 as [Q_ret [H1 H2]].
  apply path_to_statement_app in H1.
  apply semax_seq_inv' in H1. unfold overridePost in H1.
  eapply atom_to_semax_derives with (Q1:=
    (EX Q : environ -> mpred,
                       !! DeepEmbeddedDef.semax Delta Q
                            (path_to_statement ret_atom)
                            {|
                            RA_normal := Q_ret;
                            RA_break := FALSE;
                            RA_continue := FALSE;
                            RA_return := R |} && Q)%assert).
  { apply derives_refl. }
  { Intros Q. Exists Q. apply andp_right.
    apply ENTAIL_refl. apply prop_right. constructor.
    eapply semax_seq. apply H.
    apply H2.   }
  { constructor.
    eapply semax_noreturn_inv in H1;[apply H1|..].
    + apply noreturn_split_result.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  }
Qed.

Lemma atoms_conn_returns_app1: forall atoms1 atoms2 rets,
    atoms_conn_returns (atoms1 ++ atoms2) rets =
    atoms_conn_returns atoms1 rets ++ atoms_conn_returns atoms2 rets.
Proof.
  intros.
  induction atoms1.
  - rewrite app_nil_l. simpl. reflexivity.
  - rewrite <- app_comm_cons.
    simpl.
    rewrite IHatoms1.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma atoms_conn_returns_app2: forall atoms rets1 rets2 x,
    In x (atoms_conn_returns atoms (rets1++rets2)) <->
    In x (atoms_conn_returns atoms rets1 ++ atoms_conn_returns atoms rets2).
Proof.
  intros.
  induction atoms.
  - rewrite app_nil_l. simpl. reflexivity.
  - split;intro.
    + apply in_or_app. simpl in H.  apply in_app_or in H.
      destruct H.
      { rewrite map_app in H. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply in_or_app. auto.
      }
      { apply IHatoms in H. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply in_or_app. auto.
      }
    + apply in_or_app. apply in_app_or in H. destruct H.
      { rewrite map_app. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply IHatoms. apply in_or_app. auto.
      }
      {  rewrite map_app. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply IHatoms. apply in_or_app. auto.
      }
Qed.


Lemma add_return_to_atom_semax_group: forall atom atoms ret_atoms P R,
  Forall (atom_return_to_semax P R)
         (atoms_conn_returns atoms ret_atoms) ->
  In atom atoms ->
   ret_atoms <> nil ->
  atom_to_semax P (
    EX Q, Q &&
    !!(Forall (atom_return_to_semax Q R) ret_atoms)
  ) atom.
Proof.
  intros. rename H1 into H, H into H0, H0 into H1.
  destruct ret_atoms.
  - exfalso. apply H. auto.
  - induction ret_atoms.
    + destruct r as [p v]. eapply atom_to_semax_derives.
      1:{ apply derives_refl. }
      2:{ apply add_return_to_atom_semax_reverse.
          eapply Forall_forall in H0. apply H0.
          apply in_split in H1. destruct H1 as [atoms1 [atoms2 H1]].
          rewrite H1. simpl. rewrite atoms_conn_returns_app1.
          apply in_or_app. right. simpl. left. reflexivity. }
      Intros Q. Exists Q. apply andp_right. apply andp_left2. apply derives_refl.
      apply prop_right. constructor;[|constructor]. auto.
    + eapply atom_to_semax_derives.
      1:{ apply derives_refl. }
      2:{ eapply atom_to_semax_conj_rule.
          { apply IHret_atoms.
            2:{ intros C. inv C. }
            eapply Forall_forall. intros.
              eapply Forall_forall in H0. eapply H0.
              replace (r::a::ret_atoms) with ([r]++[a]++ret_atoms) by reflexivity.
              rewrite atoms_conn_returns_app2.
              replace (r::ret_atoms) with ([r]++ret_atoms) in H2 by reflexivity.
              rewrite atoms_conn_returns_app2 in H2. apply in_app_or in H2.
              destruct  H2.
              { apply in_or_app. left. auto. }
              { apply in_or_app. right. rewrite atoms_conn_returns_app2.
                apply in_or_app. auto. }
          }
          { pose proof (proj1 (Forall_forall _ _) H0 (atom ++ fst a, snd a)).
            assert ( In (atom ++ fst a, snd a) (atoms_conn_returns atoms (r :: a :: ret_atoms))).
            { replace (r::a::ret_atoms) with ([r]++[a]++ret_atoms) by reflexivity.
              rewrite atoms_conn_returns_app2. apply in_or_app. right.
              rewrite atoms_conn_returns_app2. apply in_or_app. left.
              apply in_split in H1. destruct H1 as [atoms1 [atoms2 H1]].
              rewrite H1. rewrite atoms_conn_returns_app1.
              apply in_or_app. right. simpl. left. auto. }
            specialize ( H2 H3).
            apply add_return_to_atom_semax_reverse in H2.
            apply H2.
          }
      }
      { Intros Q1. Intros Q2. Exists (andp Q1 Q2).
        apply andp_right. apply andp_left2;apply derives_refl.
        apply prop_right. eapply Forall_forall.
        intros. inv H4;[|inv H5].
        + eapply atom_return_to_semax_derives.
          { apply andp_left1. apply derives_refl. }
          { intros. apply ENTAIL_refl. }
          { eapply Forall_forall in H2. apply H2. simpl. auto. }
        + eapply atom_return_to_semax_derives.
          { apply andp_left2. apply derives_refl. }
          { intros. apply ENTAIL_refl. }
          { destruct x. apply H3. }
        +  eapply atom_return_to_semax_derives.
          { apply andp_left1. apply derives_refl. }
          { intros. apply ENTAIL_refl. }
          { eapply Forall_forall in H2. apply H2. simpl. auto. }
      }  
Qed.

  
Lemma atom_conn_atom_to_semax_reverse: forall atom1 atom2 P R,
  atom_to_semax P R (atom1 ++  atom2) ->
  atom_to_semax P (EX Q, Q && !!
                 ( atom_to_semax Q R atom2)) atom1.
Proof.
  intros.
  inv H. apply path_to_statement_app in H0.
  apply semax_seq_inv' in H0. unfold overridePost in H0.
  eapply atom_to_semax_derives with (Q1:=
   (EX Q : environ -> mpred,
                       !! DeepEmbeddedDef.semax Delta Q 
                            (path_to_statement atom2)
                            {|
                            RA_normal := R;
                            RA_break := FALSE;
                            RA_continue := FALSE;
                            RA_return := fun _ : option val => FALSE |} && Q)%assert).
  { apply derives_refl. }
  { Intros Q. Exists Q. apply andp_right.
    apply ENTAIL_refl. apply prop_right. constructor.
    auto. }
  { constructor. auto. }
Qed.


Lemma atoms_conn_atoms_app1: forall atoms1 atoms2 rets,
    atoms_conn_atoms (atoms1 ++ atoms2) rets =
    atoms_conn_atoms atoms1 rets ++ atoms_conn_atoms atoms2 rets.
Proof.
  intros.
  induction atoms1.
  - rewrite app_nil_l. simpl. reflexivity.
  - rewrite <- app_comm_cons.
    simpl.
    rewrite IHatoms1.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma atoms_conn_atoms_app2: forall atoms rets1 rets2 x,
    In x (atoms_conn_atoms atoms (rets1++rets2)) <->
    In x (atoms_conn_atoms atoms rets1 ++ atoms_conn_atoms atoms rets2).
Proof.
  intros.
  induction atoms.
  - rewrite app_nil_l. simpl. reflexivity.
  - split;intro.
    + apply in_or_app. simpl in H.  apply in_app_or in H.
      destruct H.
      { rewrite map_app in H. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply in_or_app. auto.
      }
      { apply IHatoms in H. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply in_or_app. auto.
      }
    + apply in_or_app. apply in_app_or in H. destruct H.
      { rewrite map_app. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply IHatoms. apply in_or_app. auto.
      }
      {  rewrite map_app. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply IHatoms. apply in_or_app. auto.
      }
Qed.



Lemma atom_conn_atom_to_semax_reverse_group: forall atom atoms1 atoms2 P R,
    Forall (atom_to_semax P R)
         (atoms_conn_atoms atoms1 atoms2) ->
    In atom atoms1 ->
    atoms2 <> nil ->
  atom_to_semax P (
    EX Q, Q &&
    !!(Forall (atom_to_semax Q R) atoms2)
  ) atom.
Proof.
  intros. rename H1 into H, H into H0, H0 into H1.
  destruct atoms2.
  - exfalso. apply H. auto.
  - induction atoms2.
    + eapply atom_to_semax_derives.
      1:{ apply derives_refl. }
      2:{ apply atom_conn_atom_to_semax_reverse.
          eapply Forall_forall in H0. apply H0.
          apply in_split in H1. destruct H1 as [atoms'1 [atoms'2 H1]].
          rewrite H1. unfold atoms_conn_atoms. rewrite flat_map_concat_map.
          rewrite map_app. simpl. rewrite concat_app. rewrite concat_cons.
          apply in_or_app. right. simpl. left. reflexivity. }
      Intros Q. Exists Q. apply andp_right. apply andp_left2. apply derives_refl.
      apply prop_right. constructor;[|constructor]. auto.
    + eapply atom_to_semax_derives.
      1:{ apply derives_refl. }
      2:{ eapply atom_to_semax_conj_rule.
          { apply IHatoms2.
            2:{ intros C. inv C. }
            eapply Forall_forall. intros.
              eapply Forall_forall in H0. eapply H0.
              replace (p::a::atoms2) with ([p]++[a]++atoms2) by reflexivity.
              rewrite atoms_conn_atoms_app2.
              replace (p::atoms2) with ([p]++atoms2) in H2 by reflexivity.
              rewrite atoms_conn_atoms_app2 in H2. apply in_app_or in H2.
              destruct  H2.
              { apply in_or_app. left. auto. }
              { apply in_or_app. right. rewrite atoms_conn_atoms_app2.
                apply in_or_app. auto. }
          }
          { pose proof (proj1 (Forall_forall _ _) H0 (atom++a)).
            assert ( In (atom ++ a) (atoms_conn_atoms atoms1 (p :: a :: atoms2))).
            { replace (p::a::atoms2) with ([p]++[a]++atoms2) by reflexivity.
              rewrite atoms_conn_atoms_app2. apply in_or_app. right.
              rewrite atoms_conn_atoms_app2. apply in_or_app. left.
              apply in_split in H1. destruct H1 as [atoms'1 [atoms'2 H1]].
              rewrite H1. rewrite atoms_conn_atoms_app1.
              apply in_or_app. right. simpl. left. auto. }
            specialize ( H2 H3).
            apply atom_conn_atom_to_semax_reverse in H2.
            apply H2.
          }
      }
      { Intros Q1. Intros Q2. Exists (andp Q1 Q2).
        apply andp_right. apply andp_left2;apply derives_refl.
        apply prop_right. eapply Forall_forall.
        intros. inv H4;[|inv H5].
        + eapply atom_to_semax_derives.
          { apply andp_left1. apply derives_refl. }
          { intros. apply ENTAIL_refl. }
          { eapply Forall_forall in H2. apply H2. simpl. auto. }
        + eapply atom_to_semax_derives.
          { apply andp_left2. apply derives_refl. }
          { intros. apply ENTAIL_refl. }
          {  apply H3. }
        +  eapply atom_to_semax_derives.
          { apply andp_left1. apply derives_refl. }
          { intros. apply ENTAIL_refl. }
          { eapply Forall_forall in H2. apply H2. simpl. auto. }
      }  
Qed.


Ltac merge_Q Q1 Q2:=
  Intros Q1; Intros Q2; Exists (andp Q1 Q2); apply andp_right;
  [ apply derives_refl|
    apply prop_right; repeat split;auto].

Ltac merge_Q1 Q:=
  Intros Q; Exists Q; apply andp_right;
    [apply derives_refl|
     apply prop_right; repeat split;auto].

Ltac merge_Q3 Q1 Q2 Q3:=
  Intros Q1; Intros Q2; Intros Q3; Exists (Q1 && (Q2 && Q3)); apply andp_right;
  [ apply derives_refl|
    apply prop_right; repeat split;auto].

Ltac merge_Q4 Q1 Q2 Q3 Q4:=
  Intros Q1; Intros Q2; Intros Q3; Intros Q4;
  Exists (Q1 && (Q2 && (Q3 && Q4))); apply andp_right;
  [ apply derives_refl|
    apply prop_right; repeat split;auto].

Ltac merge_Q5 Q1 Q2 Q3 Q4 Q5:=
  Intros Q1; Intros Q2; Intros Q3; Intros Q4; Intros Q5;
  Exists (Q1 && (Q2 && (Q3 && (Q4 && Q5)))); apply andp_right;
  [ apply derives_refl|
    apply prop_right; repeat split;auto].

Lemma atom_return_to_semax_derives_pre_group: forall P1 P2 Q atoms,
  P1 |-- P2 ->
  Forall (atom_return_to_semax P2 Q) atoms ->
  Forall (atom_return_to_semax P1 Q) atoms.
Proof. 
  intros.
  eapply Forall_forall.
  intros. eapply atom_return_to_semax_derives_pre.
  apply H. eapply Forall_forall in H0. apply H0. auto.
Qed.

Lemma add_pre_to_semax_derives_group: forall P1 P2 pres,
  P1 |-- P2 ->
  Forall (add_pre_to_semax P2) pres ->
  Forall (add_pre_to_semax P1) pres.
Proof. 
  intros.
  eapply Forall_forall.
  intros. eapply add_pre_to_semax_derives.
  apply H. eapply Forall_forall in H0. apply H0. auto.
Qed.

Lemma atom_to_semax_derives_pre: forall p P1 P2 Q,
  P1 |-- P2 ->
  atom_to_semax P2 Q p ->
  atom_to_semax P1 Q p.
Proof.
  intros.
  eapply atom_to_semax_derives.
  - apply H.
  - apply ENTAIL_refl.
  - auto.
Qed.

Lemma atom_to_semax_derives_pre_group: forall P1 P2 Q atoms,
  P1 |-- P2 ->
  Forall (atom_to_semax P2 Q) atoms ->
  Forall (atom_to_semax P1 Q) atoms.
Proof. 
  intros.
  eapply Forall_forall.
  intros. eapply atom_to_semax_derives_pre.
  apply H. eapply Forall_forall in H0. apply H0. auto.
Qed.

Lemma atom_to_semax_derives_post: forall p P Q1 Q2,
  ENTAIL Delta, Q1 |-- Q2 ->
  atom_to_semax P Q1 p ->
  atom_to_semax P Q2 p.
Proof.
  intros.
  eapply atom_to_semax_derives.
  - apply derives_refl.
  - apply H.
  - auto.
Qed.

Ltac solve_split:=
match goal with
| E: Forall (atom_return_to_semax _ ?R) ?ret_atoms 
  |- Forall (atom_return_to_semax ?Q ?R) ?ret_atoms => 
    eapply atom_return_to_semax_derives_pre_group;[|apply E];solve_andp
| E: Forall (atom_to_semax _ ?R) ?ret_atoms 
    |- Forall (atom_to_semax ?Q ?R) ?ret_atoms => 
      eapply atom_to_semax_derives_pre_group;[|apply E];solve_andp
| E: Forall (add_pre_to_semax _) ?pres 
  |- Forall (add_pre_to_semax _) ?pres => 
    eapply add_pre_to_semax_derives_group;[|apply E];solve_andp
end.


Lemma remove_entail: forall P Q,
  P |-- Q ->
  ENTAIL Delta, P |-- Q.
Proof.
  intros. apply andp_left2. auto.
Qed.


Ltac combine_aux_post_auto:=
  match goal with
    | E1: add_post_to_semax _ _ ,
      E2: add_post_to_semax _ _ ,
      E3: add_post_to_semax _ _ ,
      E4: add_post_to_semax _ _ ,
      E5: add_post_to_semax _ _ |-
      add_post_to_semax _ _ =>
      let Q1 := fresh "Q" in
      let Q2 := fresh "Q" in
      let Q3 := fresh "Q" in
      let Q4 := fresh "Q" in
      let Q5 := fresh "Q" in
      eapply add_post_to_semax_derives;
      [|eapply add_post_to_semax_conj_rule;
         [apply E1|
          eapply add_post_to_semax_conj_rule;
          [apply E2|
           eapply add_post_to_semax_conj_rule;
           [apply E3|
            eapply add_post_to_semax_conj_rule;
            [apply E4|apply E5]]]]];
      try (apply remove_entail);
      merge_Q5 Q1 Q2 Q3 Q4 Q5; solve_split
    | E1: add_post_to_semax _ _ ,
      E2: add_post_to_semax _ _ ,
      E3: add_post_to_semax _ _ ,
      E4: add_post_to_semax _ _  |-
      add_post_to_semax _ _ =>
      let Q1 := fresh "Q" in
      let Q2 := fresh "Q" in
      let Q3 := fresh "Q" in
      let Q4 := fresh "Q" in
      eapply add_post_to_semax_derives;
      [|eapply add_post_to_semax_conj_rule;
         [apply E1|
          eapply add_post_to_semax_conj_rule;
          [apply E2|
           eapply add_post_to_semax_conj_rule;
           [apply E3|apply E4]]]];
           try (apply remove_entail);
           merge_Q4 Q1 Q2 Q3 Q4; solve_split
    | E1: add_post_to_semax _ _ ,
      E2: add_post_to_semax _ _ ,
      E3: add_post_to_semax _ _ |-
      add_post_to_semax _ _ =>
      let Q1 := fresh "Q" in
      let Q2 := fresh "Q" in
      let Q3 := fresh "Q" in
      eapply add_post_to_semax_derives;
      [|eapply add_post_to_semax_conj_rule;
         [apply E1|
         eapply add_post_to_semax_conj_rule;[apply E2|apply E3]]];
         try (apply remove_entail);
         merge_Q3 Q1 Q2 Q3; solve_split
    | E1: add_post_to_semax _ _ ,
      E2: add_post_to_semax _ _ |-
      add_post_to_semax _ _ =>
      let Q1 := fresh "Q" in
      let Q2 := fresh "Q" in
      eapply add_post_to_semax_derives;
        [|eapply add_post_to_semax_conj_rule;[apply E1|apply E2]];
        try (apply remove_entail);
      merge_Q Q1 Q2; solve_split
    | E1: add_post_to_semax _ _ |-
      add_post_to_semax _ _ =>
      let Q1 := fresh "Q" in
      eapply add_post_to_semax_derives;
      [|apply E1];try (apply remove_entail);
      merge_Q1 Q1
    | _ => idtac
   end.


Ltac combine_aux_atom_auto:=
  match goal with
    | E1: atom_to_semax _ _ _ ,
      E2: atom_to_semax _ _ _ ,
      E3: atom_to_semax _ _ _ ,
      E4: atom_to_semax _ _ _ ,
      E5: atom_to_semax _ _ _ |-
      atom_to_semax _ _ _ =>
      let Q1 := fresh "Q" in
      let Q2 := fresh "Q" in
      let Q3 := fresh "Q" in
      let Q4 := fresh "Q" in
      let Q5 := fresh "Q" in
      eapply atom_to_semax_derives_post;
      [|eapply atom_to_semax_conj_rule;
         [apply E1|
          eapply atom_to_semax_conj_rule;
          [apply E2|
           eapply atom_to_semax_conj_rule;
           [apply E3|
            eapply atom_to_semax_conj_rule;
            [apply E4|apply E5]]]]];
            try (apply remove_entail);
      merge_Q5 Q1 Q2 Q3 Q4 Q5; solve_split
    | E1: atom_to_semax _ _ _ ,
      E2: atom_to_semax _ _ _ ,
      E3: atom_to_semax _ _ _ ,
      E4: atom_to_semax _ _ _  |-
      atom_to_semax _ _ _ =>
      let Q1 := fresh "Q" in
      let Q2 := fresh "Q" in
      let Q3 := fresh "Q" in
      let Q4 := fresh "Q" in
      eapply atom_to_semax_derives_post;
      [|eapply atom_to_semax_conj_rule;
         [apply E1|
          eapply atom_to_semax_conj_rule;
          [apply E2|
           eapply atom_to_semax_conj_rule;
           [apply E3|apply E4]]]];try (apply remove_entail);
      merge_Q4 Q1 Q2 Q3 Q4; solve_split
    | E1: atom_to_semax _ _ _ ,
      E2: atom_to_semax _ _ _ ,
      E3: atom_to_semax _ _ _ |-
      atom_to_semax _ _ _ =>
      let Q1 := fresh "Q" in
      let Q2 := fresh "Q" in
      let Q3 := fresh "Q" in
      eapply atom_to_semax_derives_post;
      [|eapply atom_to_semax_conj_rule;
         [apply E1|
         eapply atom_to_semax_conj_rule;[apply E2|apply E3]]];
         try (apply remove_entail);
      merge_Q3 Q1 Q2 Q3; solve_split
    | E1: atom_to_semax _ _ _ ,
      E2: atom_to_semax _ _ _ |-
      atom_to_semax _ _ _ =>
      let Q1 := fresh "Q" in
      let Q2 := fresh "Q" in
      eapply atom_to_semax_derives_post;
        [|eapply atom_to_semax_conj_rule;[apply E1|apply E2]];
        try (apply remove_entail);
        merge_Q Q1 Q2; solve_split
    | E1: atom_to_semax _ _ _ |-
      atom_to_semax _ _ _ =>
      let Q1 := fresh "Q" in
      eapply atom_to_semax_derives_post;
      try (apply remove_entail);
      [|apply E1];merge_Q1 Q1
    | _ => idtac
   end. 




Lemma soundness_seq_inv_aux1:  forall l1 l2 l3 l4 l5 R1 R2 R3 R4 x,
  ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] /\ l5 = []) ->
  (l1 <> [] -> add_post_to_semax (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Q R1) l1) x) ->
  (l2 <> [] -> add_post_to_semax (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Q R2) l2) x) ->
  (l3 <> [] -> add_post_to_semax (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Q R3) l3) x) ->
  (l4 <> [] -> add_post_to_semax (EX Q : assert, Q &&
                                    !! Forall (atom_return_to_semax Q R4) l4) x) ->
   (l5 <> [] -> add_post_to_semax (EX Q : assert, Q &&
                                         !! Forall (add_pre_to_semax Q) l5) x) ->
    add_post_to_semax
      (EX Q: assert,
             Q &&
             !! (Forall (atom_to_semax Q R1) l1 /\
                 Forall (atom_to_semax Q R2) l2 /\
                 Forall (atom_to_semax Q R3) l3 /\
                 Forall (atom_return_to_semax Q R4) l4 /\
                 Forall (add_pre_to_semax Q) l5)) x.
Proof.
  intros.
  destruct l1,l2,l3,l4,l5;
  try specialize (H0 nil_cons);
    try specialize (H1 nil_cons);
      try specialize (H2 nil_cons);
        try specialize (H3 nil_cons);
        try specialize (H4 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_post_auto.
Qed.



Lemma soundness_seq_inv_aux2:  forall l1 l2 l3 l4 l5 R1 R2 R3 R4 P x ,
  ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] /\ l5 = []) ->
  (l1 <> [] -> atom_to_semax P  (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Q R1) l1) x) ->
  (l2 <> [] -> atom_to_semax P (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Q R2) l2) x) ->
  (l3 <> [] -> atom_to_semax P (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Q R3) l3) x) ->
  (l4 <> [] -> atom_to_semax P (EX Q : assert, Q &&
                                    !! Forall (atom_return_to_semax Q R4) l4) x) ->
   (l5 <> [] ->atom_to_semax P (EX Q : assert, Q &&
                                         !! Forall (add_pre_to_semax Q) l5) x) ->
    atom_to_semax P
      (EX Q: assert,
             Q &&
             !! (Forall (atom_to_semax Q R1) l1 /\
                 Forall (atom_to_semax Q R2) l2 /\
                 Forall (atom_to_semax Q R3) l3 /\
                 Forall (atom_return_to_semax Q R4) l4 /\
                 Forall (add_pre_to_semax Q) l5)) x.
Proof.
  intros.
  destruct l1,l2,l3,l4,l5;
  try specialize (H0 nil_cons);
    try specialize (H1 nil_cons);
      try specialize (H2 nil_cons);
        try specialize (H3 nil_cons);
        try specialize (H4 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_atom_auto.
Qed. 


    
Lemma atom_to_semax_sem: forall x  R,
 (atom_to_semax 
        (EX Q : assert,
          !! (atom_to_semax Q R x) && Q)) R
      x.
Proof.
  intros.
  constructor. Intros Q.
  apply semax_extract_prop.
  intros. inv H.
  apply H0.
Qed.

  
Lemma atom_return_to_semax_sem: forall x R,
 (atom_return_to_semax 
        (EX Q : assert,
          !! (atom_return_to_semax Q R x) && Q)) R
      x.
Proof.
  intros. destruct x as [p v].
  constructor. Intros Q.
  apply semax_extract_prop.
  intros. inv H.
  apply H1.
Qed.


Lemma typed_true_or_typed_false: forall a,
  bool_type (typeof a) = true ->
  ENTAIL Delta, (tc_expr Delta a)
  |-- (local (liftx (typed_true (typeof a)) (eval_expr a))) ||
  (local (liftx (typed_false (typeof a)) (eval_expr a))).
Proof.
  intros.
  unfold liftx. simpl. intros x.
  unfold lift. unfold local.
  unfold lift1.
  unfold typed_true, typed_false.
  Intros. unfold tc_environ in H0.
  pose proof typecheck_expr_sound _ _ a H0.
  eapply derives_trans.
  { apply andp_right. apply derives_refl.
    apply H1. }
  apply derives_extract_prop'. intros.
  eapply expr_lemmas.tc_bool_val with (v:= eval_expr a x) in H;auto.
  destruct (strict_bool_val (eval_expr a x) (typeof a)).
  { destruct b.
    - apply orp_right1. apply prop_right. auto.
    - apply orp_right2. apply prop_right. auto.
  }
  destruct H. inv H.
Qed.

Lemma typed_true_or_typed_false': forall a,
  bool_type (typeof a) = true ->
  ENTAIL Delta, (tc_expr Delta (Eunop Onotbool a (Tint I32 Signed noattr)))
  |-- (local (liftx (typed_true (typeof a)) (eval_expr a))) ||
  (local (liftx (typed_false (typeof a)) (eval_expr a))).
Proof.
  intros.
  unfold liftx. simpl. intros x.
  unfold lift. unfold local.
  unfold lift1.
  unfold typed_true, typed_false.
  Intros. unfold tc_environ in H0.
  pose proof typecheck_expr_sound _ _ a H0.
  eapply derives_trans.
  { apply andp_right. apply derives_refl.
    eapply derives_trans;[|apply H1].
    unfold tc_expr. simpl.
    rewrite denote_tc_assert_andp.
    rewrite andp_unfold. apply andp_left2.
    apply derives_refl.
  }
  apply derives_extract_prop'. intros.
  eapply expr_lemmas.tc_bool_val with (v:= eval_expr a x) in H;auto.
  destruct (strict_bool_val (eval_expr a x) (typeof a)).
  { destruct b.
    - apply orp_right1. apply prop_right. auto.
    - apply orp_right2. apply prop_right. auto.
  }
  destruct H. inv H.
Qed.
(*
ENTAIL Delta, allp_fun_id Delta && P
|-- |==> |> FF
         || !! (bool_type (typeof a) = true) &&
            (EX P' : environ -> mpred,
             !! (split_Semax
                   (P' && local (liftx (typed_true (typeof a)) (eval_expr a)))
                   Q res1 /\
                 split_Semax
                   (P' &&
                    local (liftx (typed_false (typeof a)) (eval_expr a))) Q
                   res2) && (P' && tc_expr Delta (! a)%expr))

*)

Lemma add_exp_to_pre_inv_strong: forall P  (a:expr) pre,
      add_pre_to_semax P (add_exp_to_pre a pre) ->
       add_pre_to_semax (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_true (typeof a)) (@eval_expr CS a)))
                        && tc_expr Delta (Eunop Onotbool a (Tint I32 Signed noattr))
                        && !! (bool_type (typeof a) = true )
                        )
                         pre .
Proof.
  intros.
  destruct pre0 as [a2 p2].
  simpl in H. induction a2.
  + inv H. simpl in H1.
    eapply semax_seq_inv in H1.
    destruct H1 as [Q [H1 H2]].
    unfold overridePost in H1.
    apply DeepEmbedded.semax_ifthenelse_inv in H1.
    constructor. eapply semax_conseq with (R':={|
        RA_normal := a0;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      solve_andp.
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
    Intros P'. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros [E1 E2]. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros E3. eapply semax_conseq;[..|apply H2].
    { apply semax_skip_inv in E1. unfold RA_normal in E1.
      apply semax_break_inv in E2. unfold RA_break in E2.
      eapply derives_trans.
      { simpl; intros. apply andp_right. apply derives_refl.
        rewrite andp_comm. rewrite andp_assoc. apply andp_left2.
        rewrite andp_comm. apply typed_true_or_typed_false' in E3.
        simpl in E3. specialize (E3 x).
        rewrite <- andp_assoc.  apply andp_left1. apply E3.
      }
      simpl. intros.
      rewrite andp_comm. rewrite distrib_orp_andp.
      simpl in E1,E2. specialize (E1 x). specialize (E2 x).
      apply orp_left.
      { eapply derives_trans;[|apply E1].
        rewrite <- andp_comm. rewrite andp_assoc.
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
      { eapply derives_trans with (Q0:=|==> |> !! False || FALSE x ).
        2:{ apply bupd_mono. apply orp_left.
            apply orp_right1. apply derives_refl.
            unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2].
        rewrite <- andp_comm. rewrite andp_assoc.
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
  + constructor. intros. eapply H0.
    inv H. apply inj_pair2 in H3. subst. auto.
Qed.


Lemma add_exp_to_pre_inv: forall P  (a:expr) pre,
      add_pre_to_semax P (add_exp_to_pre a pre) ->
       add_pre_to_semax (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_true (typeof a)) (@eval_expr CS a)))
                        )
                         pre .
Proof.
  intros.
  destruct pre0 as [a2 p2].
  simpl in H. induction a2.
  + inv H. simpl in H1.
    eapply semax_seq_inv in H1.
    destruct H1 as [Q [H1 H2]].
    unfold overridePost in H1.
    apply DeepEmbedded.semax_ifthenelse_inv in H1.
    constructor. eapply semax_conseq with (R':={|
        RA_normal := a0;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      solve_andp.
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
    Intros P'. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros [E1 E2]. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros E3. eapply semax_conseq;[..|apply H2].
    { apply semax_skip_inv in E1. unfold RA_normal in E1.
      apply semax_break_inv in E2. unfold RA_break in E2.
      eapply derives_trans.
      { simpl; intros. apply andp_right. apply derives_refl.
        rewrite andp_comm. rewrite andp_assoc. apply andp_left2.
        rewrite andp_comm. apply typed_true_or_typed_false' in E3.
        simpl in E3. specialize (E3 x).
        rewrite <- andp_assoc.  apply andp_left1. apply E3.
      }
      simpl. intros.
      rewrite andp_comm. rewrite distrib_orp_andp.
      simpl in E1,E2. specialize (E1 x). specialize (E2 x).
      apply orp_left.
      { eapply derives_trans;[|apply E1].
        rewrite <- andp_comm. rewrite andp_assoc.
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
      { eapply derives_trans with (Q0:=|==> |> !! False || FALSE x ).
        2:{ apply bupd_mono. apply orp_left.
            apply orp_right1. apply derives_refl.
            unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2].
        rewrite <- andp_comm. rewrite andp_assoc.
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
  + constructor. intros. eapply H0.
    inv H. apply inj_pair2 in H3. subst. auto.
Qed.


Lemma add_exp_to_pre_inv_false: forall P  (a:expr) pre,
      add_pre_to_semax P (add_exp_to_pre (Cnot a) pre) ->
       add_pre_to_semax (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_false (typeof a)) (@eval_expr CS a)))
                        )
                         pre .
Proof.
intros.
destruct pre0 as [a2 p2].
simpl in H. induction a2.
+ inv H. simpl in H1.
  eapply semax_seq_inv in H1.
  destruct H1 as [Q [H1 H2]].
  unfold overridePost in H1.
  apply DeepEmbedded.semax_ifthenelse_inv in H1.
  constructor. eapply semax_conseq with (R':={|
      RA_normal := a0;
      RA_break := FALSE;
      RA_continue := FALSE;
      RA_return := fun _ : option val => FALSE |}).
  { eapply derives_trans;[|apply H1]. simpl. intros.
    solve_andp.
  }
  { apply derives_full_refl. }
  { apply derives_full_refl. }
  { apply derives_full_refl. }
  { intros. apply derives_full_refl. }
  Intros P'. rewrite andp_comm.
  rewrite andp_assoc. apply semax_extract_prop.
  intros [E1 E2]. rewrite andp_comm.
  rewrite andp_assoc. apply semax_extract_prop.
  intros E3. eapply semax_conseq;[..|apply H2].
  { apply semax_skip_inv in E1. unfold RA_normal in E1.
    apply semax_break_inv in E2. unfold RA_break in E2.
    eapply derives_trans.
    { simpl; intros. apply andp_right. apply derives_refl.
      rewrite andp_comm. rewrite andp_assoc. apply andp_left2.
      rewrite andp_comm. apply typed_true_or_typed_false' in E3.
      simpl in E3. specialize (E3 x).
      rewrite <- andp_assoc.  apply andp_left1. apply E3.
    }
    simpl. intros.
    rewrite andp_comm. rewrite distrib_orp_andp.
    simpl in E1,E2. specialize (E1 x). specialize (E2 x).
    apply orp_left.
    { eapply derives_trans;[|apply E1].
      rewrite <- andp_comm. rewrite andp_assoc.
      apply andp_right.
        apply andp_left1. apply derives_refl.
      rewrite andp_comm.  apply andp_right.
        repeat apply andp_left1. apply derives_refl.
      rewrite (andp_comm (allp_fun_id Delta x)).
      rewrite (andp_comm _ (P' x)). apply andp_right.
        repeat apply andp_left1. apply derives_refl.
      apply andp_left1. apply andp_left2. apply derives_refl. }
    { eapply derives_trans with (Q0:=|==> |> !! False || FALSE x ).
      2:{ apply bupd_mono. apply orp_left.
          apply orp_right1. apply derives_refl.
          unfold FALSE. unfold PROPx. simpl.
          apply derives_extract_prop. intros. tauto. }
      eapply derives_trans;[|apply E2].
      rewrite <- andp_comm. rewrite andp_assoc.
      apply andp_right.
        apply andp_left1. apply derives_refl.
      rewrite andp_comm.  apply andp_right.
        repeat apply andp_left1. apply derives_refl.
      rewrite (andp_comm (allp_fun_id Delta x)).
      rewrite (andp_comm _ (P' x)). apply andp_right.
        repeat apply andp_left1. apply derives_refl.
      apply andp_left1. apply andp_left2. apply derives_refl. }
  }
  { apply derives_full_refl. }
  { apply derives_full_refl. }
  { apply derives_full_refl. }
  { intros. apply derives_full_refl. }
+ constructor. intros. eapply H0.
  inv H. apply inj_pair2 in H3. subst. auto.
Qed.

Lemma add_exp_to_atom_inv: forall P Q (a:expr) atom,
      atom_to_semax P Q ((inl a)::atom) ->
       atom_to_semax (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_true (typeof a)) (@eval_expr CS a)))
                        ) Q atom.
Proof.
  intros. inv H.
  simpl in H0. 
  eapply semax_seq_inv in H0.
  destruct H0 as [R [H1 H2]].
  unfold overridePost in H1.
  apply DeepEmbedded.semax_ifthenelse_inv in H1.
  constructor. eapply semax_conseq with (R':={|
        RA_normal := Q;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      repeat apply andp_right.
      + apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left2. apply andp_left1. apply derives_refl.
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
    Intros P'. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros [E1 E2]. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros E3. eapply semax_conseq;[..|apply H2].
    { apply semax_skip_inv in E1. unfold RA_normal in E1.
      apply semax_break_inv in E2. unfold RA_break in E2.
      eapply derives_trans.
      { simpl; intros. apply andp_right. apply derives_refl.
        rewrite andp_comm. rewrite andp_assoc. apply andp_left2.
        rewrite andp_comm. apply typed_true_or_typed_false' in E3.
        simpl in E3. specialize (E3 x).
        rewrite <- andp_assoc.  apply andp_left1. apply E3.
      }
      simpl. intros.
      rewrite andp_comm. rewrite distrib_orp_andp.
      simpl in E1,E2. specialize (E1 x). specialize (E2 x).
      apply orp_left.
      { eapply derives_trans;[|apply E1].
        rewrite <- andp_comm. rewrite andp_assoc.
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
      { eapply derives_trans with (Q0:=|==> |> !! False || FALSE x ).
        2:{ apply bupd_mono. apply orp_left.
            apply orp_right1. apply derives_refl.
            unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2].
        rewrite <- andp_comm. rewrite andp_assoc.
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
Qed.

Lemma add_exp_to_atom_inv_false: forall P Q (a:expr) atom,
      atom_to_semax P Q ((inl (Cnot a))::atom) ->
       atom_to_semax (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_false (typeof a)) (@eval_expr CS a)))
                        ) Q atom.
Proof.
  intros. inv H.
  simpl in H0. 
  eapply semax_seq_inv in H0.
  destruct H0 as [R [H1 H2]].
  unfold overridePost in H1.
  apply DeepEmbedded.semax_ifthenelse_inv in H1.
  constructor. eapply semax_conseq with (R':={|
        RA_normal := Q;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      repeat apply andp_right.
      + apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left2. apply andp_left1. apply derives_refl.
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
    Intros P'. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros [E1 E2]. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros E3. eapply semax_conseq;[..|apply H2].
    { apply semax_skip_inv in E1. unfold RA_normal in E1.
      apply semax_break_inv in E2. unfold RA_break in E2.
      eapply derives_trans.
      { simpl; intros. apply andp_right. apply derives_refl.
        rewrite andp_comm. rewrite andp_assoc. apply andp_left2.
        rewrite andp_comm. apply typed_true_or_typed_false' in E3.
        simpl in E3. specialize (E3 x).
        rewrite <- andp_assoc.  apply andp_left1. apply E3.
      }
      simpl. intros.
      rewrite andp_comm. rewrite distrib_orp_andp.
      simpl in E1,E2. specialize (E1 x). specialize (E2 x).
      apply orp_left.
      { eapply derives_trans;[|apply E1].
        rewrite <- andp_comm. rewrite andp_assoc.
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
      { eapply derives_trans with (Q0:=|==> |> !! False || FALSE x ).
        2:{ apply bupd_mono. apply orp_left.
            apply orp_right1. apply derives_refl.
            unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2].
        rewrite <- andp_comm. rewrite andp_assoc.
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
Qed.

Lemma add_exp_to_atom_inv': forall P Q (a:expr) atom,
      atom_to_semax P Q ((inl a)::atom) ->
       atom_to_semax (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_true (typeof a)) (@eval_expr CS a)))
                        && (!! (bool_type (typeof a) = true))
                        ) Q atom.
Proof.
  intros. inv H.
  simpl in H0. 
  eapply semax_seq_inv in H0.
  destruct H0 as [R [H1 H2]].
  unfold overridePost in H1.
  apply DeepEmbedded.semax_ifthenelse_inv in H1.
  constructor. eapply semax_conseq with (R':={|
        RA_normal := Q;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      repeat apply andp_right.
      + apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left2. apply andp_left1.
        apply andp_left1. apply derives_refl.
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
    Intros P'. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros [E1 E2]. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros E3. eapply semax_conseq;[..|apply H2].
    { apply semax_skip_inv in E1. unfold RA_normal in E1.
      apply semax_break_inv in E2. unfold RA_break in E2.
      eapply derives_trans.
      { simpl; intros. apply andp_right. apply derives_refl.
        rewrite andp_comm. rewrite andp_assoc. apply andp_left2.
        rewrite andp_comm. apply typed_true_or_typed_false' in E3.
        simpl in E3. specialize (E3 x).
        rewrite <- andp_assoc.  apply andp_left1. apply E3.
      }
      simpl. intros.
      rewrite andp_comm. rewrite distrib_orp_andp.
      simpl in E1,E2. specialize (E1 x). specialize (E2 x).
      apply orp_left.
      { eapply derives_trans;[|apply E1].
        rewrite <- andp_comm. rewrite andp_assoc.
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
      { eapply derives_trans with (Q0:=|==> |> !! False || FALSE x ).
        2:{ apply bupd_mono. apply orp_left.
            apply orp_right1. apply derives_refl.
            unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2].
        rewrite <- andp_comm. rewrite andp_assoc.
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
Qed.

Lemma add_exp_to_return_atom_inv: forall P Q (a:expr) atom,
      atom_return_to_semax P Q (add_exp_to_return_atom a atom) ->
      atom_return_to_semax (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_true (typeof a)) (@eval_expr CS a)))
                        ) Q atom.
Proof.
  intros. destruct atom as [atom ret_val]. inv H.
  simpl in H1. 
  eapply semax_seq_inv in H1.
  destruct H1 as [R' [H1 H0]].
  eapply semax_seq_inv in H1.
  destruct H1 as [R [H1 H2]].
  unfold overridePost in H1.
  apply DeepEmbedded.semax_ifthenelse_inv in H1.
  constructor.
  eapply semax_seq;[..|apply H0].
  unfold overridePost.
  eapply semax_noreturn_inv with (Post:={|
    RA_normal := R';RA_break:=FALSE;RA_continue:=FALSE;RA_return:=(fun _ => FALSE)
  |});try reflexivity.
  { apply noreturn_split_result. }
  eapply semax_conseq with (R':={|
        RA_normal := R';
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      repeat apply andp_right.
      + apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left2. apply andp_left1.
        apply derives_refl.
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
    Intros P'. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros [E1 E2]. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros E3. 
    eapply semax_noreturn_inv with (Post:={|
      RA_normal:=R';RA_break:=FALSE;RA_continue:=FALSE;RA_return:=Q
    |});try reflexivity. { apply noreturn_split_result. }
    eapply semax_conseq;[..|apply H2].
    { apply semax_skip_inv in E1. unfold RA_normal in E1.
      apply semax_break_inv in E2. unfold RA_break in E2.
      eapply derives_trans.
      { simpl; intros. apply andp_right. apply derives_refl.
        rewrite andp_comm. rewrite andp_assoc. apply andp_left2.
        rewrite andp_comm. apply typed_true_or_typed_false' in E3.
        simpl in E3. specialize (E3 x).
        rewrite <- andp_assoc.  apply andp_left1. apply E3.
      }
      simpl. intros.
      rewrite andp_comm. rewrite distrib_orp_andp.
      simpl in E1,E2. specialize (E1 x). specialize (E2 x).
      apply orp_left.
      { eapply derives_trans;[|apply E1].
        solve_andp. }
      { eapply derives_trans with (Q0:=|==> |> !! False || FALSE x ).
        2:{ apply bupd_mono. apply orp_left.
            apply orp_right1. apply derives_refl.
            unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2].
        solve_andp. }
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
Qed.

Lemma add_exp_to_return_atom_inv_false: forall P Q (a:expr) atom,
      atom_return_to_semax P Q (add_exp_to_return_atom (Cnot a) atom) ->
      atom_return_to_semax (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_false (typeof a)) (@eval_expr CS a)))
                        ) Q atom.
Proof.
  intros. destruct atom as [atom ret_val]. inv H.
  simpl in H1. 
  eapply semax_seq_inv in H1.
  destruct H1 as [R' [H1 H0]].
  eapply semax_seq_inv in H1.
  destruct H1 as [R [H1 H2]].
  unfold overridePost in H1.
  apply DeepEmbedded.semax_ifthenelse_inv in H1.
  constructor.
  eapply semax_seq;[..|apply H0].
  unfold overridePost.
  eapply semax_noreturn_inv with (Post:={|
    RA_normal := R';RA_break:=FALSE;RA_continue:=FALSE;RA_return:=(fun _ => FALSE)
  |});try reflexivity.
  { apply noreturn_split_result. }
  eapply semax_conseq with (R':={|
        RA_normal := R';
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      repeat apply andp_right.
      + apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left2. apply andp_left1.
        apply derives_refl.
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
    Intros P'. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros [E1 E2]. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros E3. 
    eapply semax_noreturn_inv with (Post:={|
      RA_normal:=R';RA_break:=FALSE;RA_continue:=FALSE;RA_return:=Q
    |});try reflexivity. { apply noreturn_split_result. }
    eapply semax_conseq;[..|apply H2].
    { apply semax_skip_inv in E1. unfold RA_normal in E1.
      apply semax_break_inv in E2. unfold RA_break in E2.
      eapply derives_trans.
      { simpl; intros. apply andp_right. apply derives_refl.
        rewrite andp_comm. rewrite andp_assoc. apply andp_left2.
        rewrite andp_comm. apply typed_true_or_typed_false' in E3.
        simpl in E3. specialize (E3 x).
        rewrite <- andp_assoc.  apply andp_left1. apply E3.
      }
      simpl. intros.
      rewrite andp_comm. rewrite distrib_orp_andp.
      simpl in E1,E2. specialize (E1 x). specialize (E2 x).
      apply orp_left.
      { eapply derives_trans;[|apply E1].
        solve_andp. }
      { eapply derives_trans with (Q0:=|==> |> !! False || FALSE x ).
        2:{ apply bupd_mono. apply orp_left.
            apply orp_right1. apply derives_refl.
            unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2].
        solve_andp. }
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
Qed.


Lemma add_exp_to_pres_list_in: forall x pres a, In x pres -> In (add_exp_to_pre a x) (add_exp_to_pres a pres).
Proof.
  intros.
  induction pres.
  - inv H.
  - destruct H;subst.
    + left. auto.
    + right. auto.
Qed.

Lemma add_exp_to_atoms_list_in: forall a x atoms,
 In x atoms ->
 In (inl a :: x) (add_exp_to_atoms a atoms).
Proof.
  intros.
  induction atoms.
  - inv H.
  - destruct H;subst.
    + left. auto.
    + right. auto.
Qed.

Lemma add_exp_to_return_atoms_list_in: forall a x atoms,
In x atoms ->
In (add_exp_to_return_atom a x) (add_exp_to_return_atoms a atoms).
Proof.
intros.
induction atoms.
- inv H.
- destruct H;subst.
  + left. unfold add_exp_to_return_atom. destruct x. auto.
  + right. auto.
Qed.

Lemma add_exp_to_pre_tc: forall P a pre', 
  add_pre_to_semax P (add_exp_to_pre a pre') ->
  exists (c1' c2' : Clight.statement) (Q' : ret_assert),
    semax Delta P (Clight.Sifthenelse a c1' c2') Q'.
Proof.
  intros. destruct pre'. induction p.
  - inv H. simpl in H1. apply semax_seq_inv in H1. destruct H1 as [Q' [? ?]].
     exists Clight.Sskip, Clight.Sbreak, (overridePost Q'
             {| RA_normal := a0;
                RA_break := FALSE;
                RA_continue := FALSE;
                RA_return := fun _ : option val => FALSE |}).
    apply H.
  - pose proof HA. destruct H1 as [x _].
    specialize (H0 x). eapply H0. simpl in H.
    inv H. apply inj_pair2 in H3. subst.
    specialize (H2 x). auto. 
Qed.

Lemma add_exp_to_atom_tc: forall P Q a normal_atom',
  atom_to_semax P Q (inl a :: normal_atom') ->
  exists (c1' c2' : Clight.statement) (Q' : ret_assert),
    semax Delta P (Clight.Sifthenelse a c1' c2') Q'.
Proof.
  intros. inv H. simpl in H0.
  apply semax_seq_inv in H0. destruct H0 as [Q' [? ?]].
  exists Clight.Sskip, Clight.Sbreak, (overridePost Q'
          {| RA_normal := Q;
             RA_break := FALSE;
             RA_continue := FALSE;
             RA_return := fun _ : option val => FALSE |}).
  apply H.
Qed.

Lemma add_exp_to_return_atom_tc: forall P Q a return_atom',
atom_return_to_semax P Q (add_exp_to_return_atom a return_atom') ->
exists (c1' c2' : Clight.statement) (Q' : ret_assert),
  semax Delta P (Clight.Sifthenelse a c1' c2') Q'.
Proof.
  intros. destruct return_atom'. inv H. simpl in H1.
  apply semax_seq_inv in H1. destruct H1 as [Q'' [? ?]].
  apply semax_seq_inv in H. destruct H as [Q' [? ?]].  
  exists Clight.Sskip, Clight.Sbreak, (overridePost Q'
          (overridePost Q''
          {| RA_normal := FALSE;
             RA_break := FALSE;
             RA_continue := FALSE;
             RA_return := Q |})).
  apply H.
Qed.

(** Aux lemmas for single invariant loop soundness *)
Lemma split_not_empty_incr: forall stm res,
 continue_atom res = [] ->
 path_split stm res ->
  ~ (pre res = [] /\ normal_atom res = []
     /\ break_atom res = []  /\ return_atom res = []).
Proof.
  intros. apply split_not_empty in H0.
  intros C. apply H0. tauto.
Qed.

Lemma path_to_semax_given_sem: forall X (HX:Non_empty_Type X) ass' p,
  path_to_semax (Given_assert X HX ass', p) ->
  forall x:X, path_to_semax (ass' x, p).
Proof.
  intros. revert x.
  inv H. apply inj_pair2 in H1. subst.
  auto.
Qed.

Lemma split_loop_inv1_conn_pre1_inv: forall inv pres1,
  Forall path_to_semax
       (posts_conn_pres [(Basic_partial inv, [])] pres1)
  -> Forall (add_pre_to_semax inv) pres1.
Proof.
  intros.
  induction pres1.
  + constructor.
  + constructor.
    - destruct a. apply Forall_app in H.
      destruct H as [H1 _]. induction p.
      * constructor. inv H1. inv H2. auto.
      * constructor. intros x. apply H.
        inv H1. eapply path_to_semax_given_sem in H3.
        simpl.
        destruct (p x) eqn:E;(constructor;[rewrite <- E; apply H3| constructor]).
      (*         
        inv H3. inv H2 apply inj_pair2 in H1. subst.
        specialize (H1 x).
        simpl in H1. simpl. destruct (p x) eqn:E. 
        { constructor;[|constructor]. auto. }
        { constructor;[|constructor]. auto. } *)
    - simpl in H. apply Forall_app in H. apply proj2 in H.
      auto.
Qed.

Lemma split_loop_inv1_conn_atom1_inv: forall inv Q atoms,
  Forall (add_post_to_semax Q)
       (posts_conn_atoms [(Basic_partial inv, [])] atoms)
  -> Forall (atom_to_semax inv Q) atoms.
Proof.
  intros.
  apply Forall_forall. intros.
  assert (E: In  (Basic_partial inv, x) 
    (posts_conn_atoms [(Basic_partial inv, [])] atoms)).
  { apply in_split in H0. destruct H0 as [l1 [l2 H0]].
    rewrite H0. unfold posts_conn_atoms.
    rewrite flat_map_concat_map. simpl.
    rewrite map_app. rewrite app_nil_r.
    apply in_or_app. right. left. simpl.
    auto.  }
  eapply Forall_forall in H. 2:{ apply E. }
  constructor. inv H. auto.
Qed.

Lemma split_loop_inv1_conn_return1_inv: forall inv Q atoms,
  Forall (add_return_to_semax Q)
       (posts_conn_returns [(Basic_partial inv, [])] atoms)
  -> Forall (atom_return_to_semax inv Q) atoms.
Proof.
  intros.
  apply Forall_forall. intros.
  destruct x as [p v].
  assert (E: In  (Basic_partial inv, p, v) 
    (posts_conn_returns [(Basic_partial inv, [])] atoms)).
  { apply in_split in H0. destruct H0 as [l1 [l2 H0]].
    rewrite H0. unfold posts_conn_returns.
    rewrite flat_map_concat_map. simpl.
    rewrite map_app. rewrite app_nil_r.
    apply in_or_app. right. left. simpl.
    auto.  }
  eapply Forall_forall in H. 2:{ apply E. }
  constructor. inv H. auto.
Qed.


Lemma atoms_conn_inv_basic: forall atoms inv,
  all_basic ((atoms_conn_pres atoms [(Basic_partial inv, [])])) = true.
Proof.
  intros.
  induction atoms.
  - reflexivity.
  - simpl. auto.
Qed. 


Lemma add_post_to_semax_reverse_group2:
forall post posts atoms R, 
  In post posts ->
  Forall (add_post_to_semax R)
      (posts_conn_atoms posts atoms) -> atoms <> nil ->
  add_post_to_semax (
    EX Q, Q &&
    !!(Forall (atom_to_semax Q R) atoms)
  ) post.
Proof.
  intros.
  apply (add_post_to_semax_reverse_group post atoms R);auto.
  apply Forall_forall. intros. eapply Forall_forall in H0. apply H0.
  apply in_split in H. destruct H as [posts1 [posts2 H]].
  rewrite H in *. unfold posts_conn_atoms.
  rewrite flat_map_concat_map. rewrite map_app. simpl.
  rewrite concat_app. apply in_or_app. right.
  rewrite concat_cons. apply in_or_app. left. auto.
Qed.

Lemma add_return_to_semax_reverse_group2:
forall post posts atoms R, 
  In post posts ->
  Forall (add_return_to_semax R)
      (posts_conn_returns posts atoms) -> atoms <> nil ->
  add_post_to_semax (
    EX Q, Q &&
    !!(Forall (atom_return_to_semax Q R) atoms)
  ) post.
Proof.
  intros.
  apply (add_return_to_semax_reverse_group post atoms R);auto.
  apply Forall_forall. intros. eapply Forall_forall in H0. apply H0.
  apply in_split in H. destruct H as [posts1 [posts2 H]].
  rewrite H in *. unfold posts_conn_returns.
  rewrite flat_map_concat_map. rewrite map_app. simpl.
  rewrite concat_app. apply in_or_app. right.
  rewrite concat_cons. apply in_or_app. left. auto.
Qed.

Lemma imp_trans: forall {A B C}, (A -> B) -> (B -> C) -> (A -> C). 
Proof. tauto. Qed.

Lemma posts_inv_semax_sem: forall atoms inv post,
  (add_post_to_semax (EX Q : assert, Q &&
  !! Forall (add_pre_to_semax Q)
      (atoms_conn_pres atoms [(Basic_partial inv, [])])) post) -> 
  add_post_to_semax (EX Q : assert, Q && 
    !! (Forall (atom_to_semax Q inv) atoms)) post.
Proof.
  intros. eapply add_post_to_semax_derives;[|apply H].
  Intros Q. Exists Q. 
  apply andp_left2. apply andp_right;[apply derives_refl|].
  apply prop_right. eapply Forall_forall. intros.
  eapply Forall_forall with (x:= (Basic_partial inv, x)) in H0.
  - inv H0. constructor. auto.
  - apply in_split in H1. destruct H1 as [l1 [l2 H1]].
    rewrite H1.
    unfold atoms_conn_pres. rewrite flat_map_concat_map.
    rewrite map_app. rewrite concat_app. simpl.
    apply in_or_app. right. left. rewrite app_nil_r. auto.
Qed.

Lemma atoms_inv_semax_sem: forall inv1 inv2 atoms atom,
atom_to_semax inv1
  (EX Q : assert, Q &&
  !! Forall (add_pre_to_semax Q)
        (atoms_conn_pres atoms [(Basic_partial inv2, [])])) atom
-> atom_to_semax inv1
(EX Q : assert, Q &&
!! Forall (atom_to_semax Q inv2) atoms) atom.
Proof.
  intros. eapply atom_to_semax_derives_post;[|apply H].
  Intros Q. Exists Q. 
  apply andp_left2. apply andp_right;[apply derives_refl|].
  apply prop_right. eapply Forall_forall. intros.
  eapply Forall_forall with (x:= (Basic_partial inv2, x)) in H0.
  - inv H0. constructor. auto.
  - apply in_split in H1. destruct H1 as [l1 [l2 H1]].
    rewrite H1.
    unfold atoms_conn_pres. rewrite flat_map_concat_map.
    rewrite map_app. rewrite concat_app. simpl.
    apply in_or_app. right. left. rewrite app_nil_r. auto.
Qed.


Lemma atoms_conn_inv_not_nil: forall atoms inv, 
  atoms <> nil ->
  atoms_conn_pres atoms [(Basic_partial inv, [])] <> [].
Proof.
  intros. destruct atoms. exfalso; apply H; auto.
  simpl. intros C. inv C.
Qed.
(* 
Lemma split_loop_normal_post1_conn_wp_inv: forall 
  inv Qr Qn normal_posts1
  pres2 normal_atoms2 break_atoms2 return_atoms2
  (Ebasic1: all_basic normal_posts1 = true)
  (Ebasic2: all_basic pres2 = true),
  ~ (pres2 = [] /\ normal_atoms2 = []
     /\ break_atoms2 = []  /\ return_atoms2 = []) ->
    Forall path_to_semax
        (posts_conn_pres normal_posts1 pres2) ->
    Forall path_to_semax
      (posts_conn_pres normal_posts1
        (atoms_conn_pres normal_atoms2 [(Basic_partial inv, [])])) ->
    Forall (add_post_to_semax Qn)
        (posts_conn_atoms normal_posts1 break_atoms2) ->
    Forall (add_return_to_semax Qr)
        (posts_conn_returns normal_posts1 return_atoms2) ->
    Forall
      (add_post_to_semax
        (EX Q' : assert, Q' &&
          !! (Forall (add_pre_to_semax Q') pres2 /\
              Forall (atom_to_semax Q' inv) normal_atoms2 /\
              Forall (atom_return_to_semax Q' Qr) return_atoms2 /\
              Forall (atom_to_semax Q' Qn) break_atoms2)))
        normal_posts1.
Proof.
  intros. eapply Forall_forall.
  intros. destruct x as [a1 p1]. destruct a1.
  2:{ inv Ebasic1. apply all_basic_sem in H4; tauto. }
  pose proof path_conn_to_semax_reverse_group2' _ _ _ _ H4 Ebasic2 H0.
  pose proof path_conn_to_semax_reverse_group2' _ _ _ _ H4 (atoms_conn_inv_basic _ _) H1.
  pose proof add_post_to_semax_reverse_group2 _ _ _ _ H4 H2.
  pose proof add_return_to_semax_reverse_group2 _ _ _ _ H4 H3.
  pose proof atoms_conn_inv_not_nil normal_atoms2 inv.
  pose proof imp_trans H9 H6; clear H9 H6.
  pose proof posts_inv_semax_sem normal_atoms2 inv (Basic_partial a,p1).
  pose proof imp_trans H10 H6; clear H10 H6.
  destruct pres2,break_atoms2,return_atoms2,normal_atoms2;
  try specialize (H5 nil_cons);
    try specialize (H7 nil_cons);
      try specialize (H8 nil_cons);
        try specialize (H9 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_post_auto.
Qed. *)



(* Lemma split_loop_continue_post1_conn_wp_inv: forall 
  inv Qr Qn continue_posts1
  pres2 normal_atoms2 break_atoms2 return_atoms2
  (Ebasic1: all_basic continue_posts1 = true)
  (Ebasic2: all_basic pres2 = true),
  ~ (pres2 = [] /\ normal_atoms2 = []
     /\ break_atoms2 = []  /\ return_atoms2 = []) ->
  Forall path_to_semax
    (posts_conn_pres continue_posts1
      (atoms_conn_pres normal_atoms2 [(Basic_partial inv, [])])) ->
  Forall path_to_semax
    (posts_conn_pres continue_posts1 pres2) ->
  Forall (add_post_to_semax Qn)
    (posts_conn_atoms continue_posts1 break_atoms2) ->
  Forall (add_return_to_semax Qr)
    (posts_conn_returns continue_posts1 return_atoms2) ->
  Forall
    (add_post_to_semax
      (EX Q' : assert, Q' &&
        !! (Forall (add_pre_to_semax Q') pres2 /\
            Forall (atom_to_semax Q' inv) normal_atoms2 /\
            Forall (atom_return_to_semax Q' Qr) return_atoms2 /\
            Forall (atom_to_semax Q' Qn) break_atoms2)))
    continue_posts1.
Proof.
  intros.
  eapply split_loop_normal_post1_conn_wp_inv;auto.
Qed. *)

(* 
Lemma split_loop_normal_atoms1_conn_wp_inv: forall 
  inv Qr Qn normal_atoms1
  pres2 normal_atoms2 break_atoms2 return_atoms2
  (Ebasic2: all_basic pres2 = true),
  ~ (pres2 = [] /\ normal_atoms2 = []
     /\ break_atoms2 = []  /\ return_atoms2 = []) ->
  Forall path_to_semax
    (posts_conn_pres [(Basic_partial inv, [])]
        (atoms_conn_pres normal_atoms1 pres2)) ->
  Forall path_to_semax
    (posts_conn_pres [(Basic_partial inv, [])]
      (atoms_conn_pres normal_atoms1
        (atoms_conn_pres normal_atoms2 [(Basic_partial inv, [])]))) ->
  Forall (add_return_to_semax Qr)
    (posts_conn_returns [(Basic_partial inv, nil)]
      (atoms_conn_returns normal_atoms1 return_atoms2)) ->
  Forall (add_post_to_semax Qn)
    (posts_conn_atoms [(Basic_partial inv, nil)]
      (atoms_conn_atoms normal_atoms1 break_atoms2)) ->
  Forall
    (atom_to_semax inv
      (EX Q' : assert, Q' &&
        !! (Forall (add_pre_to_semax Q') pres2 /\
            Forall (atom_to_semax Q' inv) normal_atoms2 /\
            Forall (atom_return_to_semax Q' Qr) return_atoms2 /\
            Forall (atom_to_semax Q' Qn) break_atoms2)))
    normal_atoms1.
Proof.
  intros. eapply Forall_forall.
  intros.
  apply split_loop_inv1_conn_pre1_inv in H0.
  apply split_loop_inv1_conn_pre1_inv in H1.
  apply split_loop_inv1_conn_atom1_inv in H3.
  apply split_loop_inv1_conn_return1_inv in H2.
  pose proof atom_conn_pres_to_semax_reverse_group2' _ _ _ _ H4 Ebasic2 H0.
  pose proof atom_conn_pres_to_semax_reverse_group2' _ _ _ _ H4 (atoms_conn_inv_basic _ _) H1.
  pose proof atoms_conn_inv_not_nil normal_atoms2 inv.
  pose proof imp_trans H7 H6;clear H7 H6.
  pose proof atoms_inv_semax_sem inv inv normal_atoms2 x.
  pose proof imp_trans H8 H6;clear H8 H6.
  pose proof add_return_to_atom_semax_group _ _ _ _ _ H2 H4.
  pose proof atom_conn_atom_to_semax_reverse_group _ _ _ _ _ H3 H4.
  destruct pres2,break_atoms2,return_atoms2,normal_atoms2;
  try specialize (H5 nil_cons);
    try specialize (H7 nil_cons);
      try specialize (H6 nil_cons);
        try specialize (H8 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_atom_auto.
Qed. *)

(* Lemma split_loop_inv1_conn_break_atoms1_inv: forall Qn inv break_atoms1,
  Forall (add_post_to_semax Qn)
	  (posts_conn_atoms [(Basic_partial inv, nil)] break_atoms1)
  -> Forall (atom_to_semax inv Qn) break_atoms1.
Proof.
  intros. apply Forall_forall.
  (* eapply Forall_forall with (x:= ) *)
Admitted. *)

(* 
Lemma split_loop_continue_atoms1_conn_wp_inv: forall 
  inv Qr Qn continue_atoms1
  pres2 normal_atoms2 break_atoms2 return_atoms2,
  ~ (pres2 = [] /\ normal_atoms2 = []
     /\ break_atoms2 = []  /\ return_atoms2 = []) ->
  Forall path_to_semax
    (posts_conn_pres [(Basic_partial inv, [])]
      (atoms_conn_pres continue_atoms1
        (atoms_conn_pres normal_atoms2 [(Basic_partial inv, [])]))) ->
  Forall path_to_semax
    (posts_conn_pres [(Basic_partial inv, [])]
      (atoms_conn_pres continue_atoms1 pres2)) ->
  Forall (add_post_to_semax Qn)
    (posts_conn_atoms [(Basic_partial inv, [])]
      (atoms_conn_atoms continue_atoms1 break_atoms2)) ->
  Forall (add_return_to_semax Qr)
    (posts_conn_returns [(Basic_partial inv, nil)]
      (atoms_conn_returns continue_atoms1 return_atoms2)) ->
  Forall
    (atom_to_semax inv
      (EX Q' : assert, Q' &&
        !! (Forall (add_pre_to_semax Q') pres2 /\
            Forall (atom_to_semax Q' inv) normal_atoms2 /\
            Forall (atom_return_to_semax Q' Qr) return_atoms2 /\
            Forall (atom_to_semax Q' Qn) break_atoms2)))
    continue_atoms1.
Admitted. *)




(* Lemma split_loop_inv1_conn_return_atoms1_inv: forall inv Qr return_atoms1,
  Forall (add_return_to_semax Qr)
	  (posts_conn_returns [(Basic_partial inv, nil)] return_atoms1)
  -> Forall (atom_return_to_semax inv Qr) return_atoms1.
Admitted.


Lemma split_loop_inv1_conn_normal_posts1_inv: forall inv normal_posts2,
Forall path_to_semax
	(posts_conn_pres normal_posts2 [(Basic_partial inv, [])]) ->
Forall (add_post_to_semax inv) normal_posts2.
Admitted. *)

Ltac in_split_result S1 :=
  apply Forall_forall; intros; eapply Forall_forall in S1;[apply S1|];
  repeat (apply in_or_app;auto;right).


Lemma pack_assert_into_posts_app: forall  x inv posts,
  In x posts->
  In (pack_assert_into_post inv x) (pack_assert_into_posts inv posts).
Proof.
  induction posts.
  - auto.
  - intros. destruct H.
    + subst. left. auto.
    + right. tauto.
Qed.

Lemma pack_assert_into_post_sem: forall inv post,
  path_to_semax (pack_assert_into_post inv post) ->
  (add_post_to_semax inv) post.
Proof.
  intros. destruct post as [a1 p].
  induction a1.
  - inv H. constructor. auto.
  - simpl in *. constructor. intros. apply H0.
    inv H. apply inj_pair2 in H3. subst. apply H2.
Qed.

Lemma pack_assert_into_post_group: forall inv posts,
  Forall path_to_semax (pack_assert_into_posts inv posts) ->
  Forall (add_post_to_semax inv) posts.
Proof.
  intros. apply Forall_forall. intros.
  apply pack_assert_into_post_sem.
  eapply Forall_forall in H.
  apply H. apply pack_assert_into_posts_app. auto.
Qed.

Lemma pack_assert_into_atom_sem: forall inv1 atom inv2,
  path_to_semax (post_conn_bind_pre 
    (Basic_partial inv2, []) atom inv1) ->
  (atom_to_semax inv1 inv2) atom.
Proof.
  intros. simpl in H. rewrite app_nil_r in H.
  inv H. constructor.
  auto.
Qed.

Lemma pack_assert_into_atom_group: forall inv1 atoms inv2,
  Forall path_to_semax (posts_conn_pres [(Basic_partial inv1, [])]
    (atoms_conn_pres atoms [(Basic_partial inv2, [])])) ->
  Forall (atom_to_semax inv1 inv2) atoms.
Proof.
  intros. apply Forall_forall. intros.
  apply pack_assert_into_atom_sem.
  eapply Forall_forall in H.
  apply H. apply in_split in H0. destruct H0 as [l1 [l2 H0]].
  rewrite H0. rewrite atoms_conn_pres_app1.
  unfold posts_conn_pres. rewrite flat_map_concat_map.
  rewrite map_app. rewrite concat_app. apply in_or_app. right.
  left. simpl. reflexivity.
Qed.


Lemma pack_assert_into_atom_half_sem: forall inv1 atom inv2,
  add_post_to_semax inv2 (post_conn_atom
    (Basic_partial inv1, []) atom) ->
  (atom_to_semax inv1 inv2) atom.
Proof.
  intros. simpl in H.
  inv H. constructor.
  auto.
Qed.

Lemma pack_assert_into_atom_half_group: forall inv1 atoms inv2,
  Forall (add_post_to_semax inv2) (posts_conn_atoms 
      [(Basic_partial inv1, [])] atoms) ->
  Forall (atom_to_semax inv1 inv2) atoms.
Proof.
  intros. apply Forall_forall. intros.
  apply pack_assert_into_atom_half_sem.
  eapply Forall_forall in H.
  apply H. simpl. rewrite app_nil_r.
  apply in_split in H0. destruct H0 as [l1 [l2 H0]].
  rewrite H0. 
  rewrite map_app. apply in_or_app. right.
  left. simpl. reflexivity.
Qed.
  

Lemma pack_assert_into_ret_atom_half_sem: forall inv1 atom inv2,
  add_return_to_semax inv2 (post_conn_return
    (Basic_partial inv1, []) (fst atom) (snd atom)) ->
  (atom_return_to_semax inv1 inv2) atom.
Proof.
  intros. destruct atom. simpl in H.
  inv H. constructor.
  auto.
Qed.

Lemma pack_assert_into_ret_atom_half_group: forall inv1 atoms inv2,
  Forall (add_return_to_semax inv2) (posts_conn_returns 
      [(Basic_partial inv1, [])] atoms) ->
  Forall (atom_return_to_semax inv1 inv2) atoms.
Proof.
  intros. apply Forall_forall. intros.
  apply pack_assert_into_ret_atom_half_sem.
  eapply Forall_forall in H.
  apply H. simpl. rewrite app_nil_r.
  apply in_split in H0. destruct H0 as [l1 [l2 H0]].
  rewrite H0. 
  rewrite map_app. apply in_or_app. right.
  left. simpl. reflexivity.
Qed.


Theorem soundness: forall 
(P:assert) (Q:ret_assert) (stm: statement) (c_stm: Clight.statement)
(s: split_result),
path_split stm s ->
split_Semax P Q s ->
AClight_to_Clight stm c_stm ->
@semax CS Espec Delta P c_stm Q.
Proof.
  intros. generalize dependent c_stm. 
  generalize dependent P.
  generalize dependent Q.
  induction H.
  + intros. inv H3.
    apply inj_pair2 in H6. subst.
    pose proof bind_result_add_inv _ _ _ _ _ _ H2 H.
    (* non empty type is also used here *)
    destruct HX as [? ?].
    apply (H1 x);auto.
  + intros R P Hvalid c_stm Hc. inv Hc.
    eapply semax_seq
      with (Q:=
      EX Q:assert, andp (
        !!
          (Forall (atom_return_to_semax Q (RA_return R)) (return_atom res2)
          /\ Forall (atom_to_semax Q (RA_break R)) (break_atom res2)
          /\ Forall (atom_to_semax Q (RA_continue R)) (continue_atom res2)
          /\ Forall (atom_to_semax Q (RA_normal R)) (normal_atom res2)
          /\ Forall (add_pre_to_semax Q) (pre res2))
        ) Q
      ).
{
  apply IHpath_split1;[|apply H4].
  destruct Hvalid as [? [? [? [? [? [? [? [? [? ?]]]]]]]]];simpl in *.
  repeat split.
  + apply Forall_app in H2. apply H2.
  + apply Forall_app in H3. apply H3.
  + apply Forall_forall.
    intros.
    eapply add_post_to_semax_derives  with (Q:= EX Q: assert, Q && !!
             (Forall (atom_to_semax Q (RA_normal R)) (normal_atom res2) /\
              Forall (atom_to_semax Q (RA_break R)) (break_atom res2) /\
          Forall (atom_to_semax Q (RA_continue R)) (continue_atom res2) /\
         Forall (atom_return_to_semax Q (RA_return R)) (return_atom res2) /\
      Forall (add_pre_to_semax Q) (pre res2)
             )).
    2:{
      pose proof add_post_to_semax_reverse_group
           x (normal_atom res2) (RA_normal R) as E1.
      assert ( Forall (add_post_to_semax (RA_normal R))
                      (map (post_conn_atom x) (normal_atom res2))) as E1'.
      { apply Forall_forall. intros. eapply Forall_forall in H5.
        apply H5. apply in_or_app. right. unfold posts_conn_atoms.
        apply in_flat_map.
        exists x;auto. }
      specialize (E1 E1');clear E1'.
      pose proof add_post_to_semax_reverse_group
           x (break_atom res2) (RA_break R) as E2.
      assert ( Forall (add_post_to_semax (RA_break R))
                      (map (post_conn_atom x) (break_atom res2))) as E2'.
      { apply Forall_forall. intros. eapply Forall_forall in H7.
        apply H7. apply in_or_app. right.
        apply in_or_app. right. unfold posts_conn_atoms.
        apply in_flat_map.
        exists x;auto. }
      specialize (E2 E2');clear E2'.
      pose proof add_post_to_semax_reverse_group
           x (continue_atom res2) (RA_continue R) as E3.
      assert ( Forall (add_post_to_semax (RA_continue R))
                      (map (post_conn_atom x) (continue_atom res2))) as E3'.
      { apply Forall_forall. intros. eapply Forall_forall in H8.
        apply H8. apply in_or_app. right.
        apply in_or_app. right. unfold posts_conn_atoms.
        apply in_flat_map.
        exists x;auto. }
      specialize (E3 E3');clear E3'.
     pose proof add_return_to_semax_reverse_group
           x (return_atom res2) (RA_return R) as E4.
      assert ( Forall (add_return_to_semax (RA_return R))
         (map
            (fun ret_atom : path * option expr =>
             post_conn_return x (fst ret_atom) (snd ret_atom)) 
            (return_atom res2))) as E4'.
      { apply Forall_forall. intros. eapply Forall_forall in H9.
        apply H9. apply in_or_app. right.
        apply in_or_app. right. unfold posts_conn_returns.
        apply in_flat_map.
        exists x;auto. }
      specialize (E4 E4');clear E4'.
      pose proof path_conn_to_semax_reverse_group'
        x _ _ _ H14 H1 as E5.
      assert (Forall path_to_semax
                     (posts_conn_pres (normal_post res1) (pre res2))) as E5'.
      { apply Forall_forall. intros. eapply Forall_forall in H3.
        apply H3. apply in_or_app. right. apply in_or_app. right;auto. }
      specialize (E5 E5');clear E5'.
      pose proof split_not_empty _ _ H0 as E.
      eapply soundness_seq_inv_aux1;auto.
      intros C. apply E. tauto.
    }
    { Intros Q.  destruct R. simpl in *. intros env.
      Exists Q. apply andp_right.
      2:{ apply andp_left2. apply derives_refl. }
      apply prop_right. repeat split;auto. }
  + destruct R. simpl in *.
    apply Forall_app in H7. apply H7.
  + destruct R. simpl in *.
     apply Forall_app in H8. apply H8.
  + destruct R. simpl in *.
    apply Forall_app in H9. apply H9.
  + apply Forall_forall.
    intros.
    eapply atom_to_semax_derives  with (Q1:= EX Q: assert, Q && !!
             (Forall (atom_to_semax Q (RA_normal R)) (normal_atom res2) /\
              Forall (atom_to_semax Q (RA_break R)) (break_atom res2) /\
          Forall (atom_to_semax Q (RA_continue R)) (continue_atom res2) /\
         Forall (atom_return_to_semax Q (RA_return R)) (return_atom res2) /\
      Forall (add_pre_to_semax Q) (pre res2)
                                       )).
    1:{ apply derives_refl. }
    2:{
      assert(Et: (all_basic (pre res2) = true)   \/ (all_empty_atom (normal_atom res1) = true)).
      { destruct H1 . 
        - left. auto.
        - right. destruct H1. destruct H15. auto. }
      pose proof atom_conn_pres_to_semax_reverse_group3' P
           x _ _ H14 Et as E5. 
      assert (E5': Forall (add_pre_to_semax P)
                          (atoms_conn_pres (normal_atom res1) (pre res2))).
      { apply Forall_forall. intros. eapply Forall_forall in H2.
      apply H2. apply in_or_app. right. auto. }
        specialize (E5 E5');clear E5'.
      pose proof atom_conn_atom_to_semax_reverse_group _ _ _ P _ H10 H14 as E4.
      apply Forall_app in H11.
      pose proof (atom_conn_atom_to_semax_reverse_group
                    _ _ _ P _ (proj2 H11) H14) as E3.
      apply Forall_app in H12.
      pose proof (atom_conn_atom_to_semax_reverse_group
                    _ _ _ P _ (proj2 H12) H14) as E2.
      apply Forall_app in H13.
      pose proof (add_return_to_atom_semax_group _ _ _ P _ (proj2 H13) H14) as E1.
      pose proof split_not_empty _ _ H0 as E.
      eapply soundness_seq_inv_aux2;auto.
      intros C. apply E. tauto.
    }
    { Intros Q.  destruct R. simpl in *. intros env.
      Exists Q. apply andp_right.
      2:{ apply andp_left2. apply derives_refl. }
      apply prop_right. repeat split;auto. }
  + destruct R. simpl in *.
    apply Forall_app in H11. apply H11.
  + destruct R. simpl in *.
    apply Forall_app in H12. apply H12.
  + destruct R. simpl in *.
    apply Forall_app in H13. apply H13.
} (*end of part 1*)

{
  apply IHpath_split2;[|apply H6].
  repeat split;auto;apply Forall_forall;intros.
  - eapply add_pre_to_semax_derives.
    2: { apply add_pre_to_semax_sem. }
    1: { Intros Q. Exists Q.
         apply andp_right.
         + apply prop_right.
           eapply Forall_forall in H9. apply H9. auto.
         + apply derives_refl.
    }
  -  destruct Hvalid as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
     simpl in *. eapply Forall_forall in H5.
     apply H5. apply in_or_app. right. apply in_or_app. left. auto.
  - destruct Hvalid as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
    simpl in *. eapply Forall_forall in H7.
    apply H7. apply in_or_app. left;auto.
  - destruct Hvalid as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
    simpl in *. eapply Forall_forall in H8.
    apply H8. apply in_or_app. right. apply in_or_app. left;auto.
  - destruct Hvalid as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
    simpl in *. eapply Forall_forall in H9.
    apply H9. apply in_or_app. right. apply in_or_app. left;auto.
  - destruct Hvalid as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
    simpl in *. eapply Forall_forall in H10.
    apply H10. apply in_or_app. right. apply in_or_app. left;auto.
  - eapply atom_to_semax_derives.
    3: { apply atom_to_semax_sem. }
    { Intros Q. Exists Q. apply andp_right.
      - apply prop_right. eapply Forall_forall in H8.
        apply H8. auto.
      - apply derives_refl.
    }
    { apply ENTAIL_refl. }
  -  eapply atom_to_semax_derives.
    3: { apply atom_to_semax_sem. }
    { Intros Q. Exists Q. apply andp_right.
      - apply prop_right. eapply Forall_forall in H5.
        apply H5. auto.
      - apply derives_refl.
    }
    { apply ENTAIL_refl. }
  -  eapply atom_to_semax_derives.
    3: { apply atom_to_semax_sem. }
    { Intros Q. Exists Q. apply andp_right.
      - apply prop_right. eapply Forall_forall in H7.
        apply H7. auto.
      - apply derives_refl.
    }
    { apply ENTAIL_refl. }
  - eapply atom_return_to_semax_derives.
    3: { apply atom_return_to_semax_sem. }
    { Intros Q. Exists Q. apply andp_right.
      - apply prop_right. eapply Forall_forall in H3.
        apply H3. auto.
      - apply derives_refl.
    }
    { intros. apply ENTAIL_refl. }
}



  + (* Basic Case *)
    intros. inv H; inv H1; destruct H0 as [? [? [? [? [? [? [? [? [? ?]]]]]]]]];
              destruct Q as [Qn Qb Qc Qr];
              unfold RA_normal, RA_break, RA_continue, RA_return in *;
    simpl in *.
    - inv H5. inv H11. simpl in H5.
      apply semax_seq_skip in H5.
      eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply H5].       
      * apply derives_refl.
      * apply derives_extract_PROP'. intros C. destruct C.
      * apply derives_extract_PROP'. intros C. destruct C.
      * intros. apply derives_extract_PROP'. intros C. destruct C.
    - inv H5. inv H11. simpl in H5.
      apply semax_seq_skip in H5.
      eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply H5];
        unfold RA_normal, RA_break, RA_continue, RA_return in *.
      * apply derives_refl.
      * apply derives_extract_PROP'. intros C. destruct C.
      * apply derives_extract_PROP'. intros C. destruct C.
      * intros. apply derives_extract_PROP'. intros C. destruct C.
    - inv H1. inv H11. simpl in H9.
      inv H. inv H11. simpl in H1.
      econstructor;[..|apply H9].
      * eapply semax_skip_inv in H1. unfold RA_normal in H1.
        apply H1.
      * unfold RA_normal. apply derives_full_refl.
      * unfold RA_break. apply aux1_reduceR.
        apply andp_left2. apply andp_left2.
        apply derives_extract_PROP'. intros C;destruct C.
      * unfold RA_continue. apply aux1_reduceR.
        apply andp_left2. apply andp_left2.
        apply derives_extract_PROP'. intros C;destruct C.
      * unfold RA_return. intros.  apply aux1_reduceR.
        apply andp_left2. apply andp_left2.
        apply derives_extract_PROP'. intros C;destruct C.
    - inv H7. inv H11. simpl in H7.
      eapply DeepEmbeddedPracticalLogic.CSHL_MinimumLogic.semax_conseq.
      { apply semax_skip_inv in H7. apply H7. }
      { apply derives_full_refl. }
      { apply derives_full_refl. }
      { apply derives_full_refl. }
      { intros. apply derives_full_refl. }
      { unfold RA_normal. 
        replace Qc with (
          RA_continue {| RA_normal := Qn; RA_break := Qb; RA_continue := Qc; RA_return := Qr |}
        ) by reflexivity.
        apply semax_continue. }
    - inv H6. inv H11. simpl in H6.
      eapply DeepEmbeddedPracticalLogic.CSHL_MinimumLogic.semax_conseq.
      { apply semax_skip_inv in H6. apply H6. }
      { apply derives_full_refl. }
      { apply derives_full_refl. }
      { apply derives_full_refl. }
      { intros. apply derives_full_refl. }
      { unfold RA_normal. 
        replace Qb with (
          RA_break {| RA_normal := Qn; RA_break := Qb; RA_continue := Qc; RA_return := Qr |}
        ) by reflexivity.
        apply semax_break. }
    - inv H5. inv H11.
      simpl in H5.
      eapply DeepEmbeddedPracticalLogic.CSHL_MinimumLogic.semax_conseq;[..|apply semax_skip];unfold normal_ret_assert, RA_normal,
      RA_return,RA_break,RA_continue.
      { apply semax_skip_inv in H5. apply H5. }
      { apply derives_full_refl. }
      { apply aux1_reduceR. apply andp_left2.
        apply derives_extract_prop'. intros C;destruct C. }
      { apply aux1_reduceR. apply andp_left2.
        apply derives_extract_prop'. intros C;destruct C. }
      { intros. apply aux1_reduceR. apply andp_left2.
        apply derives_extract_prop'. intros C;destruct C. }
    - inv H8. inv H11. simpl in H9.
      apply semax_skip_seq in H9.
      eapply DeepEmbeddedPracticalLogic.CSHL_MinimumLogic.semax_conseq;[..|apply H9];unfold normal_ret_assert, RA_normal,
      RA_return,RA_break,RA_continue.
      { apply derives_full_refl. }
      { apply aux1_reduceR. apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
      { apply aux1_reduceR. apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
      { apply aux1_reduceR. apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
      { intros. apply derives_full_refl. }
    - inv H5. inv H11. simpl in H5. apply semax_seq_skip in H5.
      eapply DeepEmbeddedPracticalLogic.CSHL_MinimumLogic.semax_conseq;[..|apply H5];unfold normal_ret_assert, RA_normal,
      RA_return,RA_break,RA_continue;try apply derives_full_refl.
      { apply aux1_reduceR. apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
      { apply aux1_reduceR. apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
      { intros. apply aux1_reduceR. apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
+ intros.
  inv H2.
  eapply semax_conseq with (P':= (!! ((bool_type (typeof a)) = true)) &&
   (tc_expr Delta (Eunop Onotbool a (Tint I32 Signed noattr))) &&
  (
    !! (split_Semax (P && local (liftx (typed_true (typeof a)) (eval_expr a))) Q res1 /\ 
    split_Semax (P && local (liftx (typed_false (typeof a)) (eval_expr a))) Q res2
  ) && P)) (R':= Q); try (intros;apply derives_full_refl).
  2:{ rewrite andp_assoc.
      apply semax_extract_prop. intros.
      rewrite andp_comm. rewrite andp_assoc. 
      apply semax_extract_prop.
      intros [E1 E2].
      eapply semax_pre_simple.
      2:{ eapply semax_ifthenelse;auto.
      + apply IHpath_split1. apply E1. auto.
      + apply IHpath_split2. apply E2. auto. }
      solve_andp. }
    assert (exists c1' c2' Q', semax Delta P (Clight.Sifthenelse a c1' c2') Q').
    { destruct res1 as [pre1 path1 normal_post1 break_post1
                        continue_post1 return_post1 normal_atom1
                        break_atom1 continue_atom1 return_atom1].
      hnf in H1; simpl in H1; destruct H1 as 
      [S1 [S2 [S3 [S4 [S5 [S6 [S7 [S8 [S9 S10]]]]]]]]].
      apply Forall_app in S1. apply proj1 in S1.
      destruct pre1 as [|pre' pre1].
      2:{ apply Forall_inv in S1. apply add_exp_to_pre_tc in S1. auto. }
      apply Forall_app in S7. apply proj1 in S7.
      destruct normal_atom1 as [|normal_atom' normal_atom1].
      2:{ apply Forall_inv in S7. apply add_exp_to_atom_tc in S7. auto. }
      apply Forall_app in S8. apply proj1 in S8.
      destruct continue_atom1 as [|continue_atom' continue_atom1].
      2:{ apply Forall_inv in S8. apply add_exp_to_atom_tc in S8. auto. }
      apply Forall_app in S9. apply proj1 in S9.
      destruct break_atom1 as [|break_atom' break_atom1].
      2:{ apply Forall_inv in S9. apply add_exp_to_atom_tc in S9. auto. }
      apply Forall_app in S10. apply proj1 in S10.
      destruct return_atom1 as [|return_atom' return_atom1].
      2:{ apply Forall_inv in S10. apply add_exp_to_return_atom_tc in S10. auto. }
      apply split_not_empty in H. exfalso. apply H. auto. }
  destruct H2 as [c1' [c2' [Q' H2]]].
  apply semax_ifthenelse_inv in H2.
  assert (ENTAIL Delta, allp_fun_id Delta && P 
          |-- tc_expr Delta  (Eunop Onotbool a (Tint I32 Signed noattr))) as E1.
  { eapply derives_trans;[apply H2|].
    eapply derives_trans;[| apply bupd_tc_expr_cong].
    apply bupd_mono.     
    apply orp_left;[apply orp_right1;apply derives_refl|].
    apply orp_right2. apply andp_left1.
    apply andp_left2. apply derives_refl. }
    assert (ENTAIL Delta, allp_fun_id Delta && P 
    |-- !! (bool_type (typeof a) = true)) as E2.
  { simpl. intros env.
    simpl in H2. specialize (H2 env).
    eapply derives_trans;[apply H2|].
    eapply derives_trans;[|apply bupd_bool_type_cong].
    apply bupd_mono.     
    apply orp_left;[apply orp_right1;apply derives_refl|].
    apply orp_right2. apply andp_left1.
    apply andp_left1. apply derives_refl. }
  pose proof andp_right _ _ _ E1 E2.
  apply add_andp in H3.
  rewrite H3.
  apply aux1_reduceR. eapply derives_trans;[|apply bupd_intro].
  apply andp_right;[solve_andp|].
  apply andp_right;[|solve_andp].
  apply prop_right.
  hnf in H1. simpl in H1.
  destruct H1 as [S1 [S2 [S3 [S4 [S5 [S6 [S7 [S8 [S9 S10]]]]]]]]].
  repeat split.
  - apply Forall_forall. intros. apply add_exp_to_pre_inv.
    eapply Forall_forall in S1. apply S1.
    apply in_or_app. left.
    apply add_exp_to_pres_list_in. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S2. apply S2.
    apply in_or_app. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S3. apply S3.
    apply in_or_app. auto.
  - apply Forall_forall. intros. 
    eapply Forall_forall in S4. apply S4.
    apply in_or_app. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S5. apply S5.
    apply in_or_app. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S6. apply S6.
    apply in_or_app. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S7.
    apply add_exp_to_atom_inv. apply S7.
    apply in_or_app. left. apply add_exp_to_atoms_list_in. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S8.
    apply add_exp_to_atom_inv. apply S8.
    apply in_or_app. left. apply add_exp_to_atoms_list_in. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S9.
    apply add_exp_to_atom_inv. apply S9.
    apply in_or_app. left. apply add_exp_to_atoms_list_in. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S10.
    apply add_exp_to_return_atom_inv. apply S10.
    apply in_or_app. left.
    apply add_exp_to_return_atoms_list_in. auto.
  - apply Forall_forall. intros.
    apply add_exp_to_pre_inv_false.
    eapply Forall_forall in S1. apply S1.
    apply in_or_app. right.
    apply add_exp_to_pres_list_in. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S2. apply S2.
    apply in_or_app. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S3. apply S3.
    apply in_or_app. auto.
  - apply Forall_forall. intros. 
    eapply Forall_forall in S4. apply S4.
    apply in_or_app. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S5. apply S5.
    apply in_or_app. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S6. apply S6.
    apply in_or_app. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S7.
    apply add_exp_to_atom_inv_false. apply S7.
    apply in_or_app. right. apply add_exp_to_atoms_list_in. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S8.
    apply add_exp_to_atom_inv_false. apply S8.
    apply in_or_app. right. apply add_exp_to_atoms_list_in. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S9.
    apply add_exp_to_atom_inv_false. apply S9.
    apply in_or_app. right. apply add_exp_to_atoms_list_in. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S10.
    apply add_exp_to_return_atom_inv_false. apply S10.
    apply in_or_app. right.
    apply add_exp_to_return_atoms_list_in. auto.


+ (** Loop *)
  simpl. rewrite !app_nil_r. intros.
  hnf in H1;simpl in H1. destruct H1 as [S1 [S2 [S3 [_ [_ [S4 [_ [_ [_ _]]]]]]]]].
  inv S1. clear H5. simpl in H4. inv H4. simpl in H3.
  apply semax_skip_inv in H3. unfold RA_normal in H3.
  eapply semax_conseq with (R':=Q);[apply H3|..];intros;try apply derives_full_refl.
  inv H2. eapply semax_loop with (Q':= inv2).
  { apply IHpath_split1;auto. destruct Q as [Qn Qb Qc Qr]. 
    pose proof (split_not_empty_incr _ _ Econt_atom H0) as E.
    repeat split;unfold loop1_ret_assert, loop2_ret_assert, RA_normal, RA_break, RA_continue, RA_return in *.
    - apply split_loop_inv1_conn_pre1_inv. in_split_result S2.
    - in_split_result S2.
    - apply pack_assert_into_post_group. in_split_result S2.
    - in_split_result S3.
    - apply pack_assert_into_post_group. in_split_result S2.
    - in_split_result S4.
    - apply pack_assert_into_atom_group. in_split_result S2.
    - apply pack_assert_into_atom_half_group. 
      simpl. rewrite app_nil_r. in_split_result S3.
    - apply pack_assert_into_atom_group. in_split_result S2.
    - apply pack_assert_into_ret_atom_half_group.
      simpl. rewrite app_nil_r. in_split_result S4.
  }
  { apply IHpath_split2;auto. destruct Q as [Qn Qb Qc Qr]. 
    repeat split;unfold loop1_ret_assert, loop2_ret_assert, RA_normal, RA_break, RA_continue, RA_return in *.
    - apply split_loop_inv1_conn_pre1_inv. in_split_result S2.
    - in_split_result S2.
    - apply pack_assert_into_post_group. in_split_result S2.
    - in_split_result S3.
    - destruct (continue_post res2);[constructor|]. inv Econt_post.
    - in_split_result S4.
    - apply pack_assert_into_atom_group. in_split_result S2.
    - apply pack_assert_into_atom_half_group. 
      simpl. rewrite app_nil_r. in_split_result S3.
    - destruct (continue_atom res2);[constructor|]. inv Econt_atom.
    - apply pack_assert_into_ret_atom_half_group.
      simpl. rewrite app_nil_r. in_split_result S4.
  }

+ intros. inv H5.
  assert (AClight_to_Clight
    (Sloop (LIDouble inv inv) (c1;; c2) AClight.Sskip)
    (Clight.Sloop (Clight.Ssequence c_stm1 c_stm2) Clight.Sskip)
  ).
  { try repeat constructor;auto. }
  destruct H2.
  { (* no continue *)
    assert (c1' = c_stm1).
    { eapply AClight_to_Clight_unique. apply H. apply H10. }
    subst.
    specialize (IHpath_split _ _ H4 _ H5).
    apply semax_loop_inv in IHpath_split.
    destruct Q as [Qn Qb Qc Qr].
    eapply semax_conseq;[apply IHpath_split|..];
      try (intros;apply derives_full_refl).
    Intros Q1 Q2. apply semax_extract_prop.
    intros [Hq1 Hq2].
    apply semax_skip_inv in Hq2.
    unfold RA_normal, loop2_ret_assert in Hq2.
    unfold loop1_ret_assert in Hq1.
    assert (E:semax Delta Q1 (Clight.Ssequence c_stm1 c_stm2)
              {|
              RA_normal := Q1;
              RA_break := Qn;
              RA_continue := Q1;
              RA_return := Qr |}
    ).
    { eapply semax_conseq;[..|apply Hq1];
      try (intros; apply derives_full_refl);
      unfold RA_normal,RA_continue;auto. }
    apply semax_seq_inv in E.
    unfold overridePost in E.
    destruct E as [inv2 [E1 E2]].
    eapply semax_loop; unfold loop1_ret_assert, loop2_ret_assert.
    { eapply semax_nocontinue_inv;[..|apply E1];auto.
      - unfold RA_normal. reflexivity.
      - unfold RA_break. reflexivity.
      - unfold RA_return. reflexivity. }
    { eapply semax_nocontinue_inv;[..|apply E2];auto.
      assert (c2' = c_stm2).
      { eapply AClight_to_Clight_unique. apply H0. apply H11. }
      subst. auto. }
  }
  { (* c2 = skip *)
    assert (c2' = c_stm2).
    { eapply AClight_to_Clight_unique. apply H0. apply H11. }
    subst. inv H0.
    specialize (IHpath_split _ _ H4 _ H5).
    destruct Q as [Qn Qb Qc Qr].
    apply semax_loop_inv in IHpath_split.
    eapply semax_conseq;[apply IHpath_split|..];
    try (intros; apply derives_full_refl).
    Intros inv1 inv2.
    apply semax_extract_prop;unfold loop1_ret_assert, loop2_ret_assert.
    intros [E1 E2].
    assert (E:semax Delta inv1 c_stm1
              {|
              RA_normal := inv1;
              RA_break := Qn;
              RA_continue := inv1;
              RA_return := Qr |}
    ).
    { eapply semax_skip_inv in E2.
      apply semax_seq_inv in E1. unfold RA_normal in E2.
      destruct E1 as [Q' [E1 E3]].
      apply semax_skip_inv in E3. unfold RA_normal in E3.
      unfold overridePost in E1.
      eapply semax_conseq with (R' := {|
        RA_normal := inv2;
        RA_break := Qn;
        RA_continue := inv2;
        RA_return := Qr      
      |});unfold overridePost, RA_normal,
      RA_break, RA_return, RA_continue; try (intros; apply derives_full_refl);auto.
      eapply semax_conseq;[..|apply E1];unfold overridePost, RA_normal,
      RA_break, RA_return, RA_continue; try (intros; apply derives_full_refl);auto.
    }
    eapply semax_loop.
    { eapply semax_conseq;[..|apply E];unfold loop1_ret_assert, RA_normal,
      RA_break, RA_continue, RA_return;try (intros; apply derives_full_refl). }
    eapply semax_conseq;[..|eapply semax_skip];unfold normal_ret_assert;
    unfold loop2_ret_assert, RA_normal, RA_break, RA_continue, RA_return;
    [apply derives_full_refl|..];[apply derives_full_refl|..];
    try (intros; apply andp_left2; apply andp_left2; apply FF_left).
  }
Qed.

End Soundness.
