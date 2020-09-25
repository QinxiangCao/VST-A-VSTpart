Require Import AClight.AClight.
Notation "x ;; y" := (Ssequence x y)  (at level 65) : logic.
Print VST.veric.semax_lemmas.Cnot.
Check nil.
Check [nil].
Definition path:= list (expr + statement) .
Definition path_statement := (assert * path * assert)%type.
Definition path_statements := list path_statement .
Definition partial_path_statement := (path * assert)%type.
Definition partial_path_statements := list partial_path_statement.
Definition atom_seq := (list path)%type.


Record basic_split_result:Type := Pack{
  pre   : partial_path_statements;
  paths : path_statements;
  normal_post  : partial_path_statements;
  continue_post: partial_path_statements;
  break_post   : partial_path_statements;
  return_post  : partial_path_statements;
  normal_atom  : list path;
  continue_atom: list path;
  break_atom   : list path;
  return_atom  : list path;
}.


(*
Parameter sr: split_result.
Check (sr.(pre)).
Check pre sr.
*)
(**
-----------------------------------------------------------------------------
  Combine two single unit as a new one , four situations 
-----------------------------------------------------------------------------
**)
Definition partial_conn_pp (x y :partial_path_statement) : path_statement :=
match x,y with
|(path1,pre) , (path2,post) => (pre,path1++path2,post)
end.

Definition partial_conn_ll (x y :path): path := 
match x,y with
| hd1::tl1, hd2::tl2 =>  x++y
| _,_ => nil
end.

Definition partial_conn_lp (x: path)(y :partial_path_statement) : partial_path_statement :=
match y with
|(path_y,post) => (x++path_y , post)
end.

Definition partial_conn_pl (x :partial_path_statement)(y: path) : partial_path_statement :=
match x with
|(path_x,pre) => (path_x++y , pre)
end.


(**
-----------------------------------------------------------------------------
  Combine two lists consisting of basic units above as a new one , four situations 
-----------------------------------------------------------------------------
**)
Definition partial_conv_pp (x y : partial_path_statements) : path_statements :=
concat (map (fun x1 => (map (fun y1 => partial_conn_pp x1 y1) y)) x ).

Definition partial_conv_ll (x y : atom_seq) : atom_seq :=
concat (map (fun x1 => (map (fun y1 => partial_conn_ll x1 y1) y)) x ).

Definition partial_conv_pl (x:partial_path_statements)(y:atom_seq) : partial_path_statements :=
concat (map (fun x1 => (map (fun y1 => partial_conn_pl x1 y1) y)) x ).

Definition partial_conv_lp (x:atom_seq)(y:partial_path_statements): partial_path_statements :=
concat (map (fun x1 => (map (fun y1 => partial_conn_lp x1 y1) y)) x ).


(**
-----------------------------------------------------------------------------
  Add the expr as a singleton 'path' to paths. Used in if branch.
    updated : also used in do-while loop.
  Two main situations : adding to a (path * assert) , or to a (path) 
    
-----------------------------------------------------------------------------
**)
Fixpoint partial_addpre_p (pres: partial_path_statements)(e:expr):partial_path_statements:=
match pres with
|(path,assert)::tl => ((inl e)::path , assert):: (partial_addpre_p tl e)
|_ => nil
end.

Fixpoint partial_addpre_l (l:atom_seq)(e:expr):atom_seq:=
match l with
|hd::tl => ((inl e)::hd)::(partial_addpre_l tl e)
|_ => nil
end.

Fixpoint partial_addpre_m (l:atom_seq)(e:expr):atom_seq:=
match l with
|hd::tl => (hd++[(inl e)])::(partial_addpre_l tl e)
|_ => nil
end.


(**
-----------------------------------------------------------------------------
  add an assertion to partial path statements , to make path statements,
  or add an assertion to atomic sequence to create a partial path statements
-----------------------------------------------------------------------------
**)
Fixpoint partial_addpre_a (pres: partial_path_statements)(a:assert):path_statements := 
match pres with 
|(path,assert)::tl => (a,path,assert)::(partial_addpre_a tl a)
|_ => nil
end.

Fixpoint partial_addpre_b (l:atom_seq)(a:assert):partial_path_statements:=
match l with
|hd::tl => (hd,a)::(partial_addpre_b tl a)
|_ => nil
end.

Fixpoint partial_addpre_c (pres: partial_path_statements)(a:assert):path_statements := 
match pres with 
|(path,assert)::tl => (assert,path,a)::(partial_addpre_a tl a)
|_ => nil
end.


(**
-----------------------------------------------------------------------------
  Define a relationship : a statement is consisted of only atomic actions, 
  such as assignments, which means it has no assertions and is consisted of 
  only a 'path' .
  
  This will be later moved into path_split. Here is just a temporary state.
-----------------------------------------------------------------------------

Inductive path_sequence :statement -> path -> Prop:=
(* means arg1 statement is consisted of sequence of automic actions*)

|Split_assign : forall c1 l1 exp1 exp2,
  path_sequence c1 l1 ->
  path_sequence ((Sassign exp1 exp2);;c1) (inr (Sassign exp1 exp2) :: l1)

|Split_set : forall c1 l1 ident exp,
  path_sequence c1 l1 ->
  path_sequence ((Sset ident exp);;c1) (inr (Sset ident exp) :: l1)
(*
|Split_goto : forall c1 l1 label,
  path_sequence c1 l1 ->
  path_sequence ((Sgoto label);;c1) (inr (Sgoto label) :: l1)
*)
**)


Inductive split_result : Type :=
| Basic_Result:  basic_split_result -> split_result
| Binded_Result: forall A:Type, (A -> split_result) -> split_result.

Definition FALSE := (PROP (False) LOCAL () SEP ()).

Inductive basic_split : statement -> basic_split_result->Prop :=
|  (* c1 ;; c2*)
  Split_seq : forall c1 pre1 paths1 n_post1 c_post1 r_post1 b_post1 n_atom1 c_atom1 r_atom1 b_atom1 
                     c2 pre2 paths2 n_post2 c_post2 r_post2 b_post2 n_atom2 c_atom2 r_atom2 b_atom2,
    basic_split c1 (Pack pre1 paths1 n_post1 c_post1 r_post1 b_post1 n_atom1 c_atom1 r_atom1 b_atom1)->
    basic_split c2 (Pack pre2 paths2 n_post2 c_post2 r_post2 b_post2 n_atom2 c_atom2 r_atom2 b_atom2)->
    basic_split (c1;;c2)
      (Pack
        (* pre = pre1 ++  n_a1 * pre2 ++ c_a1 * pre2 *)
        (pre1 ++ (partial_conv_lp n_atom1 pre2) ++ (partial_conv_lp c_atom1 pre2))
        (* paths  = path1 ++ path2 ++ (n_post1+ c_post1) * pre2*)
        (paths1 ++ paths2 ++ (partial_conv_pp n_post1 pre2) ++ (partial_conv_pp c_post1 pre2) )
        (* n_post = n_post2 ++ (n_post1 + c_post1 + b_post1) * n_atom2 
                  = n_post2 ++ n_post1 * n_atom2 ++ c_post1 * n_atom2 ++ b_post1 * n_atom2 *)
        (n_post2 ++ (partial_conv_pl n_post1 n_atom2) ++ (partial_conv_pl c_post1 n_atom2) ++ (partial_conv_pl b_post1 n_atom2))
        (* c_post = c_post2 ++ (n_post1 + c_post1 + b_post1) * c_atom2 
                  = c_post2 ++ n_post1 * c_atom2 ++ c_post1 * c_atom2 ++ b_post1 * c_atom2 *)
        (c_post2 ++ (partial_conv_pl n_post1 c_atom2) ++ (partial_conv_pl c_post1 c_atom2) ++ (partial_conv_pl b_post1 c_atom2))
        (* r_post = r_post2 *)
        (r_post2)
        (* b_post = b_post2 ++ (n_post1 + c_post1 + b_post1) * b_atom2 
                  = b_post2 ++ n_post1 * b_atom2 ++ c_post1 * b_atom2 ++ b_post1 * b_atom2 *)
        (b_post2 ++ (partial_conv_pl n_post1 b_atom2) ++ (partial_conv_pl c_post1 b_atom2) ++ (partial_conv_pl b_post1 b_atom2))
        (* n_atom = (n_atom1 + c_atom1 + b_atom1) * n_atom2
                  = n_atom1 * n_atom2 ++ c_atom1 * n_atom2 ++ b_atom1 * n_atom2 *)
        ((partial_conv_ll n_atom1 n_atom2) ++ (partial_conv_ll c_atom1 n_atom2) ++ (partial_conv_ll b_atom1 n_atom2))
        (* c_atom = (n_atom1 + c_atom1 + b_atom1) * c_atom2
                  = n_atom1 * c_atom2 ++ c_atom1 * c_atom2 ++ b_atom1 * c_atom2 *)
        ((partial_conv_ll n_atom1 c_atom2) ++ (partial_conv_ll c_atom1 c_atom2) ++ (partial_conv_ll b_atom1 c_atom2))
        (* b_atom = (n_atom1 + c_atom1 + b_atom1) * b_atom2
                  = n_atom1 * b_atom2 ++ c_atom1 * b_atom2 ++ b_atom1 * b_atom2 *)
        ((partial_conv_ll n_atom1 b_atom2) ++ (partial_conv_ll c_atom1 b_atom2) ++ (partial_conv_ll b_atom1 b_atom2))
        (* r_atom = r_atom2 ++ (n_atom1 + c_atom1 + b_atom1) * r_atom2
                  = r_atom2 ++ n_atom1 * r_atom2 ++ c_atom1 * r_atom2 ++ b_atom1 * r_atom2 *)
        ( r_atom2 ++ (partial_conv_ll n_atom1 r_atom2) ++ (partial_conv_ll c_atom1 r_atom2) ++ (partial_conv_ll b_atom1 r_atom2))
      )

| (* if a then c1 else c2 endif *)
  Split_if : forall a c1 pre1 paths1 n_post1 c_post1 r_post1 b_post1 n_atom1 c_atom1 r_atom1 b_atom1 
                     c2 pre2 paths2 n_post2 c_post2 r_post2 b_post2 n_atom2 c_atom2 r_atom2 b_atom2,
    basic_split c1 (Pack pre1 paths1 n_post1 c_post1 r_post1 b_post1 n_atom1 c_atom1 r_atom1 b_atom1)->
    basic_split c2 (Pack pre2 paths2 n_post2 c_post2 r_post2 b_post2 n_atom2 c_atom2 r_atom2 b_atom2)->
    basic_split (Sifthenelse a c1 c2) 
   (Pack
      (* pre = a * pre1 ++ (~a) * pre2 *)
      ((partial_addpre_p pre1 a) ++ (partial_addpre_p pre2 (VST.veric.semax_lemmas.Cnot a)))
      (* paths = paths1 ++ paths2 *)
      (paths1 ++ paths2)
      (* n_post = n_post1 ++ n_post2 *)
      (n_post1 ++ n_post2)
      (* c_post = c_post1 ++ c_post2 *)
      (c_post1 ++ c_post2)
      (* r_post = r_post1 ++ r_post2 *)
      (r_post1 ++ r_post2)
      (* b_post = b_post1 ++ b_post2 *)
      (b_post1 ++ b_post2)
      (* n_atom = a * n_atom1 ++ (~a) * n_atom2*) 
      ((partial_addpre_l n_atom1 a) ++ (partial_addpre_l n_atom2 (VST.veric.semax_lemmas.Cnot a)))
      (* c_atom = a * c_atom1 ++ (~a) * c_atom2*) 
      ((partial_addpre_l c_atom1 a) ++ (partial_addpre_l c_atom2 (VST.veric.semax_lemmas.Cnot a)))
      (* r_atom = a * r_atom1 ++ (~a) * r_atom2*) 
      ((partial_addpre_l r_atom1 a) ++ (partial_addpre_l r_atom2 (VST.veric.semax_lemmas.Cnot a)))
      (* b_atom = a * b_atom1 ++ (~a) * b_atom2*) 
      ((partial_addpre_l b_atom1 a) ++ (partial_addpre_l b_atom2 (VST.veric.semax_lemmas.Cnot a)))
   )

| (* It is equivalent to a singleton of path : [[inr (Sset ident exp) ]] *)
  Split_set : forall ident exp,
  basic_split ((Sset ident exp)) 
    (Pack nil nil nil nil nil nil [[inr (Sset ident exp) ]] nil nil nil )
        
| (* it is just a singleton too. Therefore only the normal_atom will be not empty *) 
  Split_assign : forall exp1 exp2,
  basic_split (Sassign exp1 exp2)
    (Pack nil nil nil nil nil nil [[inr (Sassign exp1 exp2)]] nil nil nil )

| (* pre and normal_post not empty*) 
  Split_assert : forall a,
  basic_split (Sassert a) 
  (Pack [(nil,a)] nil [(nil,a)] nil nil nil nil nil nil nil)

| Split_continue : 
  basic_split Scontinue (Pack nil nil nil nil nil nil nil [nil] nil nil)

| Split_break : 
  basic_split Sbreak (Pack nil nil nil nil nil nil nil nil [nil] nil)
(*Print option.*)
| Split_return_Some : forall e,
  basic_split (Sreturn (Some e)) (Pack nil nil nil nil nil nil nil nil nil [[inl e]])    (* return value should not be here*)

| Split_return_None : 
  basic_split (Sreturn (None)) (Pack nil nil nil nil nil nil nil nil nil [nil])

| Split_Sskip : 
  basic_split Sskip (Pack nil nil nil nil nil nil [nil] nil nil nil)
(* The C loops are derived forms. Here are the three forms in Clight from CompCert:
i.
Definition Swhile (e: expr) (s: statement) :=
  Sloop (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip.

ii.
Definition Sdowhile (s: statement) (e: expr) :=
  Sloop s (Sifthenelse e Sskip Sbreak).

iii.
Definition Sfor (s1: statement) (e2: expr) (s3: statement) (s4: statement) :=
  Ssequence s1 (Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4).
*)
 
(* we do not allow Continue in incremental step (sure! how can incremental step have Continue?)
   thus if there is continue in incremental step , we will have to add an 'Assert False' in that list.
*)
(*and about return , void return is different from other returns. we need to both modify normal and return *)
| Split_loop_single : forall inv c1 pre1 paths1 n_post1 c_post1 r_post1 b_post1 n_atom1 c_atom1 r_atom1 b_atom1 
                     c2 pre2 paths2 n_post2 c_post2 r_post2 b_post2 n_atom2 c_atom2 r_atom2 b_atom2,
    basic_split c1 (Pack pre1 paths1 n_post1 c_post1 r_post1 b_post1 n_atom1 c_atom1 r_atom1 b_atom1)->
    basic_split c2 (Pack pre2 paths2 n_post2 c_post2 r_post2 b_post2 n_atom2 c_atom2 r_atom2 b_atom2)->
  basic_split (Sloop (LISingle inv) c1 c2)
  (Pack 
    (* pre = inv*)
      [(nil,inv)]     
    (
      (* paths = (inv,pre1) ++ 
               (inv,nc_atom1,pre2) ++ 
               (inv,nc_atom1,nc_atom2,inv) ++
               (paths1) ++ 
               (nc_post1,pre2) ++
               (nc_post1,nc_atom2,inv)++
               (paths2) ++ 
               (nc_post2,inv)
      *)
      (partial_addpre_a pre1 inv) ++ 
      (partial_addpre_a (partial_conv_lp n_atom1 pre2) inv) ++ (partial_addpre_a (partial_conv_lp c_atom1 pre2) inv) ++
      (partial_addpre_a (partial_addpre_b (partial_conv_ll n_atom1 n_atom2) inv)inv) ++ (partial_addpre_a (partial_addpre_b (partial_conv_ll n_atom1 c_atom2) inv)inv) 
        ++(partial_addpre_a (partial_addpre_b (partial_conv_ll c_atom1 n_atom2) inv)inv) ++(partial_addpre_a (partial_addpre_b (partial_conv_ll c_atom1 c_atom2) inv)inv) ++
      paths1 ++
      (partial_conv_pp n_post1 pre2) ++ (partial_conv_pp c_post1 pre2) ++
      (partial_addpre_c (partial_conv_pl n_post1 n_atom2) inv) ++(partial_addpre_c (partial_conv_pl n_post1 c_atom2) inv) ++
        (partial_addpre_c (partial_conv_pl c_post1 n_atom2) inv) ++(partial_addpre_c (partial_conv_pl c_post1 c_atom2) inv) ++
      paths2 ++
      (partial_addpre_c n_post2 inv) ++(partial_addpre_c c_post2 inv) 
      (*  
      | No break or return
      |------------------------------------------------------
      | Considering breaks : break is the exit point of the loop. Thus jump out
      | 
      | No elements.    
      | 
      |--------------------------------------------------------                                                                                                   
      | Considering returns
        Return is surely not followed by an assert, thus it will not be in the path part.
 *)
   )
    (* n_post : b_post1 ++ b_post2 ++ (inv,b_atom1) 
             ++ (nc_post1,b_atom2) ++ (inv,nc_atom1,b_atom2) *)
    (
     b_post1 ++ b_post2 ++ (partial_addpre_b b_atom1 inv) ++ 
    (partial_conv_pl n_post1 b_atom2) ++ ( partial_conv_pl c_post1 b_atom2) ++
    (partial_addpre_b (partial_conv_ll n_atom1 b_atom2)inv) ++ (partial_addpre_b (partial_conv_ll c_atom1 b_atom2)inv) 
    )
    (* c_post : nil*)
    nil 
    (* r_post : r_post1 ++ r_ post2 ++ (inv,r_atom1)
             ++ (nc_post1,r_atom2) ++ (inv,nc_atom1,r_atom2)
    *)
    (
     r_post1 ++ r_post2 ++ (partial_addpre_b r_atom1 inv) ++ 
    (partial_conv_pl n_post1 r_atom2) ++ ( partial_conv_pl c_post1 r_atom2) ++
    (partial_addpre_b (partial_conv_ll n_atom1 r_atom2)inv) ++ (partial_addpre_b (partial_conv_ll c_atom1 r_atom2)inv) 
    )
    (* b_post : *)
    nil
    (*n_atom : b_atom1 ++ (nc_atom1,b_atom2)*)
    ( b_atom1 ++ (partial_conv_ll n_atom1 b_atom2) ++ (partial_conv_ll c_atom1 b_atom2))
    (*c_atom : nil*)    
    nil
    (*r_atom : r_atom1 ++ (nc_atom1,r_atom2)*)
     ( r_atom1 ++ (partial_conv_ll n_atom1 r_atom2) ++ (partial_conv_ll c_atom1 r_atom2)) 
    (*b_atom : nil*)    
    nil)
    
| Split_loop_double : forall inv1 inv2 c1 pre1 paths1 n_post1 c_post1 r_post1 b_post1 n_atom1 c_atom1 r_atom1 b_atom1 
                     c2 pre2 paths2 n_post2 c_post2 r_post2 b_post2 n_atom2 c_atom2 r_atom2 b_atom2,
    basic_split c1 (Pack pre1 paths1 n_post1 c_post1 r_post1 b_post1 n_atom1 c_atom1 r_atom1 b_atom1)->
    basic_split c2 (Pack pre2 paths2 n_post2 c_post2 r_post2 b_post2 n_atom2 c_atom2 r_atom2 b_atom2)->
  basic_split (Sloop (LIDouble inv1 inv2) c1 c2)
  (Pack 
    (*pre*)
    [(nil,inv1)]
    (*paths = (inv1,pre1) ++
              (inv1,nc_atom1,inv2) ++ 
              (paths1) ++
              (nc_post1,inv2) ++
              (inv2,pre2) ++
              (inv2,nc_atom1,inv1) ++ 
              (paths2) ++ 
              (nc_post2,inv2) 
    *)
    (
      (partial_addpre_a pre1 inv1) ++ 
      (partial_addpre_a (partial_addpre_b (partial_conv_ll n_atom1 n_atom2) inv2)inv1) ++ (partial_addpre_a (partial_addpre_b (partial_conv_ll n_atom1 c_atom2) inv2)inv1) ++
        (partial_addpre_a (partial_addpre_b (partial_conv_ll c_atom1 n_atom2) inv2)inv1) ++(partial_addpre_a (partial_addpre_b (partial_conv_ll c_atom1 c_atom2) inv2)inv1) ++
      paths1 ++
      (partial_addpre_c n_post1 inv2) ++ (partial_addpre_c c_post1 inv2) ++ 
      (partial_addpre_a pre2 inv2) ++
      (partial_addpre_a (partial_addpre_b n_atom1 inv1)inv2) ++ (partial_addpre_a (partial_addpre_b c_atom1 inv1)inv2) ++
        (partial_addpre_a (partial_addpre_b n_atom1 inv1)inv2) ++(partial_addpre_a (partial_addpre_b c_atom1 inv1)inv2) ++
      paths2 ++
      (partial_addpre_c n_post2 inv2) ++(partial_addpre_c c_post2 inv2) 
    )
    (* n_post : b_post1 ++ b_post2 ++ (inv1,b_atom1) ++ (inv2,b_atom2)   *)
     (b_post1 ++ b_post2 ++ (partial_addpre_b b_atom1 inv1) ++ (partial_addpre_b b_atom2 inv2)) 
    (*c_post : nil*)
    nil 
    (* r_post : r_post1 ++ r_ post2 ++ (inv1,r_atom1) ++ (inv2,r_atom2) *)
    (r_post1 ++ r_post2 ++ (partial_addpre_b r_atom1 inv1) ++ (partial_addpre_b r_atom2 inv2) )
    (* b_post : nil*)
    nil
    (*n_atom : b_atom1  *)
    ( b_atom1 )
    (*c_atom : nil *)
    nil 
    (*r_atom : r_atom1 *)
    ( r_atom1 )
    (*b_atom : nil *)
    nil
   (*WHAT IF CONTINUE JUMPS THE ASSERT AND MAKES IT ATOM?
     Oh! That's an error.
   *)
  )
| Split_loop_null : forall c1 pre1 paths1 n_post1 c_post1 r_post1 b_post1 n_atom1 c_atom1 r_atom1 b_atom1 
                     c2 pre2 paths2 n_post2 c_post2 r_post2 b_post2 n_atom2 c_atom2 r_atom2 b_atom2,
    basic_split c1 (Pack pre1 paths1 n_post1 c_post1 r_post1 b_post1 n_atom1 c_atom1 r_atom1 b_atom1)->
    basic_split c2 (Pack pre2 paths2 n_post2 c_post2 r_post2 b_post2 n_atom2 c_atom2 r_atom2 b_atom2)->
  (n_atom1 = nil /\ c_atom1 = nil /\ b_atom1 = nil /\ r_atom1 = nil) \/(n_atom2 = nil /\ c_atom2 = nil /\ b_atom2 = nil /\ r_atom2 = nil) ->
  basic_split (Sloop LINull c1 c2) 
  (Pack 
    (* pre = pre1 ++ (n_atom1 + c_atom1 ) * pre2 *)
     (pre1 ++ (partial_conv_lp c_atom1 pre2) ++ (partial_conv_lp n_atom1 pre2))
    (* path = paths1 ++ 
              nc_post1 * pre2 ++ 
              paths2 ++
              n_post2 * pre1++
              (c_post2 ,FALSE)
              (nc_post1 * c_atom2,FALSE)
    *)
    ( paths1 ++ 
      partial_conv_pp n_post1 pre2 ++ partial_conv_pp c_post1 pre2 ++
      paths2 ++ 
      partial_conv_pp n_post2 pre1 ++ partial_conv_pp c_post2 pre2 ++
      partial_addpre_c c_post2 FALSE ++
      (partial_addpre_c (partial_conv_pl n_post1 c_atom2) FALSE) ++ (partial_addpre_c (partial_conv_pl c_post1 c_atom2) FALSE) 
    )
    (* n_post = (nc_post1) * n_atom2 ++ n_post2  
      ++ b_post1 ++b_post2 ++ (nc_post1,b_atom2) *)
    ((partial_conv_pl n_post1 n_atom2 ++ partial_conv_pl c_post1 n_atom2 ++ n_post2) ++
     ( b_post1 ++ b_post2 ++ (partial_conv_pl n_post1 b_atom2) ++ (partial_conv_pl c_post1 b_atom2)))
    (* c_post = nil *)
    nil
    
    (* r_post = r_post1 ++ r_post2 ++ (nc_post1,r_atom2) *)
    (r_post1 ++ r_post2 ++ (partial_conv_pl n_post1 r_atom2) ++ (partial_conv_pl c_post1 r_atom2) )

    
    (*
      b_post :nil
    *)
    
      nil nil nil nil nil

    (*
    (pre1 ++ (partial_conv_lp atom1 pre2) (* ++ (partial_conv_lp atom2 pre1) *) ) 
    (paths1++ (partial_conv_pp post1 pre2) ++ paths2 ++ (partial_conv_pp post2 pre1)) ++
    (post2 ++ (partial_conv_pl post1 atom2) (* ++ (partial_conv_pl post2 atom1) *) )
     nil
     *)
  )
  
  | (*function call regarded as atomic action , the same as assign and set.*)
  Split_func : forall ident e el,
  basic_split (Scall (ident) e el)
  (Pack nil nil nil nil nil nil [[inr (Scall (ident) e el)]] nil nil nil)
  .


(*



Definition merge_parallel (x y :basic_split_result) : basic_split_result:=
match x with
|(Pack pre1 paths1 np1 cp1 bp1 rp1 na1 ca1 ba1 ra1) 
  => match y with 
 (Pack pre2 paths2 np2 cp2 bp2 rp2 na2 ca2 ba2 ra2) 
    =>(Pack (pre1++pre2) (paths1++paths2) (np1++np2) (cp1++cp2) (bp1++bp2) (rp1++rp2)
       (na1++na2) (ca1++ca2) (ba1++ba2) (ra1++ra2))
       end
end.

Definition merge_serial (x y :basic_split_result) : basic_split_result:=
match x,y with
|(Pack pre1 paths1 n_post1 c_post1 r_post1 b_post1 n_atom1 c_atom1 r_atom1 b_atom1),
 (Pack pre2 paths2 n_post2 c_post2 r_post2 b_post2 n_atom2 c_atom2 r_atom2 b_atom2) =>
(Pack
        (pre1 ++ (partial_conv_lp n_atom1 pre2) ++ (partial_conv_lp c_atom1 pre2))
        (paths1 ++ paths2 ++ (partial_conv_pp n_post1 pre2) ++ (partial_conv_pp c_post1 pre2) )
        (n_post2 ++ (partial_conv_pl n_post1 n_atom2) ++ (partial_conv_pl c_post1 n_atom2) ++ (partial_conv_pl b_post1 n_atom2))
        (c_post2 ++ (partial_conv_pl n_post1 c_atom2) ++ (partial_conv_pl c_post1 c_atom2) ++ (partial_conv_pl b_post1 c_atom2))
        (r_post2)
        (b_post2 ++ (partial_conv_pl n_post1 b_atom2) ++ (partial_conv_pl c_post1 b_atom2) ++ (partial_conv_pl b_post1 b_atom2))
        ((partial_conv_ll n_atom1 n_atom2) ++ (partial_conv_ll c_atom1 n_atom2) ++ (partial_conv_ll b_atom1 n_atom2))
        ((partial_conv_ll n_atom1 c_atom2) ++ (partial_conv_ll c_atom1 c_atom2) ++ (partial_conv_ll b_atom1 c_atom2))
        ((partial_conv_ll n_atom1 b_atom2) ++ (partial_conv_ll c_atom1 b_atom2) ++ (partial_conv_ll b_atom1 b_atom2))
        (r_atom2 ++ (partial_conv_ll n_atom1 r_atom2) ++ (partial_conv_ll c_atom1 r_atom2) ++ (partial_conv_ll b_atom1 r_atom2))
      )
end.
*)

(** Here needs further polishment, to avoid errors about given in the second PRE part. **)
Inductive Bind  (merge_method : basic_split_result -> basic_split_result -> basic_split_result)  :
               split_result -> split_result -> split_result -> Prop :=
  | Bind_Basic: forall s1 s2,
      Bind merge_method (Basic_Result s1) (Basic_Result s2) (Basic_Result (merge_method s1 s2))
  | Bind_Left: forall (A:Type) res1 res2 res_sum,
      (forall a, Bind merge_method (res1 a) res2 (res_sum a)) ->
      Bind merge_method (Binded_Result A res1) res2 (Binded_Result A res_sum)
  | Bind_Right: forall (A:Type) res1 res2 res_sum,
      (forall a, Bind merge_method res1 (res2 a) (res_sum a)) ->
      Bind merge_method res1 (Binded_Result A res2) (Binded_Result A res_sum)
.

Parameter assert_parser : statement ->  
Inductive path_split: statement -> split_result->Prop := 
| Given: forall (A: Type) (substm: A -> statement) (subres: A -> split_result),
    (forall a:A, path_split (substm a) (subres a)) ->
    path_split (Sgiven A substm) (Binded_Result A subres)



    

(*
| Parallel: forall c1 c2 res1 res2 res,
    path_split c1 res1 ->
    path_split c2 res2 ->
    Bind merge_parallel res1 res2 res ->
    path_split (c1;;c2) res
| Serial: forall c1 c2 res1 res2 res,
    path_split c1 res1 ->
    path_split c2 res2 ->
    Bind merge_serial res1 res2 res ->
    path_split (c1;;c2) res
*)
.
Print sigT.
    

Print funspec.
Print semax.
Print Clight.statement.

Fixpoint to_Clight (stm: statement): Clight.statement.
Admitted. 

Section Soundness.

Context {CS: compspecs} {Espec: OracleKind} (Delta: tycontext).

Print path.
Fixpoint path_to_statement (path: path) : Clight.statement :=
match path with
| [] => Clight.Sskip
| hd::tl => 
  match hd with
  |inl expr => Clight.Ssequence (Clight.Sifthenelse expr Clight.Sskip Clight.Sbreak) (path_to_statement tl)
  |inr statement =>  Clight.Ssequence (to_Clight statement) (path_to_statement tl)
  end
end.


Print ret_assert.

Definition path_to_semax (path: path_statement) : Prop :=
  match path with (pre, path, post) =>
  @semax CS Espec Delta pre (path_to_statement path)
    {| RA_normal := post;
       RA_break := FALSE;
       RA_continue := FALSE;
       RA_return := fun _ => FALSE|} end.

Definition partial_pre_to_semax (pre: assert) (path: partial_path_statement) : Prop :=
  match path with (path, post) =>
  @semax CS Espec Delta pre (path_to_statement path)
    {| RA_normal := post;
    RA_break := FALSE;
    RA_continue := FALSE;
    RA_return := fun _ => FALSE|} end.

Definition partial_post_to_semax (post: assert) (path: partial_path_statement) : Prop :=
  match path with (path, pre) =>
  @semax CS Espec Delta pre (path_to_statement path)
  {| RA_normal := post;
  RA_break := FALSE;
  RA_continue := FALSE;
  RA_return := fun _ => FALSE|} end.

Definition partial_return_to_semax (post: option val -> assert) (path: partial_path_statement): Prop :=
  match path with (path, pre) =>
  @semax CS Espec Delta pre (path_to_statement path)
  {| RA_normal := FALSE;
  RA_break := FALSE;
  RA_continue := FALSE;
  RA_return := post|} end.

Definition atom_to_semax  (pre: assert) (post: assert) (path: path): Prop :=
  @semax CS Espec Delta pre (path_to_statement path)
  {| RA_normal := post;
    RA_break := FALSE;
    RA_continue := FALSE;
    RA_return := fun _ => FALSE|}.

Definition atom_return_to_semax (pre: assert) (post: option val -> assert) (path: path)  : Prop :=
  @semax CS Espec Delta pre (path_to_statement path)
  {| RA_normal := FALSE;
    RA_break := FALSE;
    RA_continue := FALSE;
    RA_return := post|}.


Definition fold_prop {A:Type} (test: A -> Prop) (list: list A) : Prop :=
  fold_left (fun H a => H /\ test a) list True.

Fixpoint to_Semax_Group (res: split_result) (P:assert) 
        (Q:ret_assert): Prop :=
  match res with
  | Binded_Result A subres =>
      forall a:A, to_Semax_Group (subres a) P Q
  | Basic_Result (Pack pre paths n_post c_post r_post b_post n_atom c_atom r_atom b_atom) =>
      fold_prop (partial_pre_to_semax P) pre
      /\ fold_prop path_to_semax paths
      /\ fold_prop (partial_post_to_semax (RA_normal Q)) n_post
      /\ fold_prop (partial_post_to_semax (RA_break Q)) b_post
      /\ fold_prop (partial_post_to_semax (RA_continue Q)) c_post
      /\ fold_prop (partial_return_to_semax (RA_return Q)) r_post
      /\ fold_prop (atom_to_semax P (RA_normal Q)) n_atom
      /\ fold_prop (atom_to_semax P (RA_break Q)) b_atom
      /\ fold_prop (atom_to_semax P (RA_continue Q)) c_atom
      /\ fold_prop (atom_return_to_semax P (RA_return Q)) r_atom
  end.

Theorem soundness: forall 
  (P:assert) (Q:ret_assert) (stm: statement) 
  (s: split_result),
  path_split stm s ->
  to_Semax_Group s P Q ->
  @semax CS Espec Delta P (to_Clight stm) Q.
Admitted.

End Soundness.


Fixpoint combine (l : list partial_path_statements) (l' : list partial_path_statements) : list (partial_path_statements*partial_path_statements) :=
      match l,l' with
        | x::tl, y::tl' => (x,y)::(combine tl tl')
        | _, _ => nil
      end.

(* list partial * list partial*)
Print combine.

Print list_prod.

(*given 
  how to define Hoare Triple (two different ones
      semax_func : 鍑芥暟鐨刪oare triple.
      semax_body : 璇彞鐨凥oare triple.
      
        鐜板湪鐨凥oare triple 涓嶆槸a triple is valid. 
          閫昏緫鏈韩鐨勫彲闈犳€ф槸 a triple is proovable -> a triple is valid.
            VST Floyd閲屾湁涓€涓� seperation logic ..aslogic..soundness.
              寮€澶村ぇ鍐� 鏈変竴浜涙帹瀵兼妧宸с€�
              VeryC鐨勬枃浠跺す涓嬮潰鏈変竴浜�
               
  function call
  ).
*)
(*To avoid curry & uncurry
Inductive split_split:
|BASIC RESULT : basic_result -> result
|Binded_R :forall A: Type (A-> splitresult)->split_result.

Define split_refule = sigma Type (fun T:Type=> T-> basic_result).


*)
