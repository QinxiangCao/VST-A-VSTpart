Require Import AClight.AClight.
Print prod.
Print sum.
Definition path:= list (expr + statement) .

Definition path_statement := (assert * path * assert)%type.

Definition path_statements := list path_statement .
  
Locate assert.
Locate environ.

Print assert.
Print environ.

Notation "x ;; y" :=
 (Ssequence x y)  (at level 65) : logic.

Definition partial_path_statement := (path * assert)%type.

Definition partial_path_statements := list partial_path_statement.

(* combine two partial_path together as a path*)
Definition partial_path_mix (x y :partial_path_statement) : path_statement :=
match x,y with
|(path1,pre) , (path2,post) => (pre,path1++path2,post)
end.

Check map.

Fixpoint combine (l : list partial_path_statements) (l' : list partial_path_statements) : list (partial_path_statements*partial_path_statements) :=
      match l,l' with
        | x::tl, y::tl' => (x,y)::(combine tl tl')
        | _, _ => nil
      end.

(* list partial * list partial*)
Print combine.
Fixpoint partial_path_list_mix (x y : partial_path_statements) : path_statements :=
match x,y with
|(path1,pre1)::tl, (path2,post2)::tl' => (pre1,path1++path2,post2)::(partial_path_list_mix tl tl')
| _, _ => nil
end.
(*concat (map (fun x1 => (map (fun y1 => partial_path_mix x1 y1) y)) x ).*)

Parameter ass_empty : (assert)%type. (* what should be here?*)

(*
expr
---
(pre,path,post)
       ||||||
    *********
    |||||

->

(pre,path,post)
        ||||||
    +*********
    ||||||
+:this expr
|:empty assert


*)
(*no more used ↓*)
Definition partial_path_addpre (pre : partial_path_statement)(e:expr) :partial_path_statement :=
match pre with
|(p,a) => ((inl e):: p,a) 
end.


Fixpoint partial_paths_addpre (pres: partial_path_statements)(e:expr):partial_path_statements:=
match pres with
|(pre1,path1)::tl => ((inl e)::pre1 , path1):: (partial_paths_addpre tl e)
|_ => nil
end.

Locate expr.



Parameter nexpr : expr->expr .
(*
Axiom wxwnb : forall (a :expr)(b :val) ,
eval_expr a b != eval_expr (nexpr a) (b) *)

(* here needs to be changed*)



Inductive path_split: statement -> 
  (partial_path_statements * path_statements * partial_path_statements) ->Prop := 
| Split_seq : forall c1 c2 pre1 pre2 path1 path2 post1 post2,
    path_split c1 (pre1,path1,post1) ->
    path_split c2 (pre2,path2,post2) ->
    path_split (c1;;c2) (pre1,path1++(partial_path_list_mix post1 pre2)++path2,post2)
(* c1 c2*)

| Split_if : forall a c1 c2 pre1 pre2 path1 path2 post1 post2,
    path_split c1 (pre1,path1,post1) ->
    path_split c2 (pre2,path2,post2) ->
    path_split (Sifthenelse a c1 c2) 
   (
    (partial_paths_addpre pre1 a)++(partial_paths_addpre pre2 (nexpr a)),
    path1++path2,
    post1++post2
    )

  (* if(a) then c1 else c2 endif*)



(*
| Split_seq: forall stm1 stm2 ps1 ps2 x y z,
    path_split ((Sassert x) ;; stm1 ;; (Sassert y)) ps1 ->
    path_split ((Sassert y) ;; stm2 ;; (Sassert z)) ps2 ->
    path_split ((Sassert x) ;; stm1 ;; (Sassert y) ;; stm2 ;; (Sassert z))
     (ps1 ++ ps2)
     
| Split_if: forall c1 c2 c3 c4 b ,
    safe_op b c2 -> safe_op b c4 -> safe_op b c3 ->
    path_split (c1 ;; b ;; c2 ;; c4) 
               (map ps1 (fun (pre c post) => (pre,c,(post /\ b = true))) ->
    path_split (c1 ;; ~ b ;; c3 ;; c4)
               (map ps2 (fun (pre,c,post) => (pre,c,(post /\ b = false))) ->
    path_split (c1 ;; Sifthenelse (b,c2,c3) ;; c4) (ps1 ++ ps2)
*)

    
.

