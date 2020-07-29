Require Import AClight.AClight.
Print prod.
Print sum.
Definition path:= list (expr + statement) .
Definition path_statement := (assert * path * assert)%type.
Definition path_statements := list path_statement .

Notation "x ;; y" := (Ssequence x y)  (at level 65) : logic.

Definition partial_path_statement := (path * assert)%type.
Definition partial_path_statements := list partial_path_statement.

Definition atom_seq := (list path)%type.

(**
-----------------------------------------------------------------------------
  Combine two single unit as a new one , four situations 
-----------------------------------------------------------------------------
**)

(* combine two partial_path together as a path*)
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
  End
-----------------------------------------------------------------------------
**)


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
  End
-----------------------------------------------------------------------------
**)


(**
-----------------------------------------------------------------------------
  Add the expr as a singleton 'path' to paths. Used in if branch. 
  Two situations : adding to a (path * assert) , or to a (path) 
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

(**
-----------------------------------------------------------------------------
  End
-----------------------------------------------------------------------------
**)


Print VST.veric.semax_lemmas.Cnot.

(**
-----------------------------------------------------------------------------
  Define a relationship : a statement is consisted of only atomic actions, 
  such as assignments, which means it has no assertions and is consisted of 
  only a 'path' .
-----------------------------------------------------------------------------
**)
Inductive path_sequence :statement -> path -> Prop:=
(* means arg1 statement is consisted of sequence of automic actions*)
|Split_skip : forall c1 l1,
  path_sequence c1 l1 ->
  path_sequence (Sskip ;; c1) ((inr Sskip)::l1)

|Split_assign : forall c1 l1 exp1 exp2,
  path_sequence c1 l1 ->
  path_sequence ((Sassign exp1 exp2);;c1) (inr (Sassign exp1 exp2) :: l1)

|Split_set : forall c1 l1 ident exp,
  path_sequence c1 l1 ->
  path_sequence ((Sset ident exp);;c1) (inr (Sset ident exp) :: l1)
 
|Split_sequence : forall c1 l1 c2 l2,
  path_sequence c1 l1 ->
  path_sequence c2 l2 ->
  path_sequence (Ssequence c1 c2) (l1++l2)
(*
|Split_goto : forall c1 l1 label,
  path_sequence c1 l1 ->
  path_sequence ((Sgoto label);;c1) (inr (Sgoto label) :: l1)
*)
.
(**
-----------------------------------------------------------------------------
  End
-----------------------------------------------------------------------------
**)

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




Inductive path_split: statement -> 
  partial_path_statements * path_statements * partial_path_statements * list path
   ->Prop := 
|  (* c1 ;; c2*)
  Split_seq : forall c1 c2 pre1 pre2 paths1 paths2 post1 post2 atom1 atom2,
    path_split c1 (pre1,paths1,post1,atom1) ->
    path_split c2 (pre2,paths2,post2,atom2) ->
    path_split (c1;;c2) 
      (pre1 ++ (partial_conv_lp atom1 pre2),
      paths1 ++ (partial_conv_pp post1 pre2) ++ paths2,
      post2 ++ (partial_conv_pl post1 atom2),
      (partial_conv_ll atom1 atom2)
      )

| (* if a then c1 else c2 endif *)
  Split_if : forall a c1 c2 pre1 pre2 paths1 paths2 post1 post2 atom1 atom2,
    path_split c1 (pre1,paths1,post1,atom1) ->
    path_split c2 (pre2,paths2,post2,atom2) ->
    path_split (Sifthenelse a c1 c2) 
   (
    (partial_addpre_p pre1 a) ++ (partial_addpre_p pre2 (VST.veric.semax_lemmas.Cnot a)),
    paths1++paths2,
    post1++post2,
   (partial_addpre_l atom1 a) ++ (partial_addpre_l atom2 (VST.veric.semax_lemmas.Cnot a))
    )
|
 (* Definition Swhile (Inv: assert) (e: expr) (s: statement):=
  Sloop (LISingle Inv) (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip.*)
  
  (** (assert + e) + s) / assert + (~e + skip)**)
  Split_loop : forall pre paths post atom inv e state,
  path_split state (pre,paths,post,atom) ->
  path_split (Swhile inv e state) 
      ( [(nil,inv)],
      ( partial_conv_pp [([(inl e);(inr Sskip)],inv)]  pre ) ++ paths,
        post ++ (partial_conv_pl [([(inl e);(inr Sskip)],inv)] atom) ++  [([(inl (VST.veric.semax_lemmas.Cnot e));(inr Sbreak)],inv)]  ,
        nil
      )
| (* atom action sequence*)
  Split_atom : forall c1 path1,
    path_sequence c1 path1 ->
    path_split c1 (nil,nil,nil,[path1])
| (* assertion *)
  (*one question , what to do with assert + assert ?*)
  Split_assert_l:forall s pre paths post atom a,
    path_split s (pre,paths,post,atom) -> 
    path_split ( (Sassert a);; s) 
      ( pre ++ (partial_addpre_b atom a),
       (partial_addpre_a pre a) ++ paths,
       post,
       nil
      )
| Split_assert_r:forall s pre paths post atom a,
    path_split s (pre,paths,post,atom) -> 
    path_split ( s ;; (Sassert a)) 
      ( pre,
       (partial_addpre_c pre a) ++ paths,
       post ++ (partial_addpre_b atom a),
       nil
      )
.


Fixpoint combine (l : list partial_path_statements) (l' : list partial_path_statements) : list (partial_path_statements*partial_path_statements) :=
      match l,l' with
        | x::tl, y::tl' => (x,y)::(combine tl tl')
        | _, _ => nil
      end.

(* list partial * list partial*)
Print combine.

Print list_prod.
