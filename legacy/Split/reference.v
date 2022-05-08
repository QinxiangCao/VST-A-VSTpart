Parameter assertion: Type.

Inductive S_stm: Type :=
| S_SAssert
| S_SSkip
| S_SSeq (s1 s2: S_stm).

Inductive C_stm: S_stm -> Type :=
| C_SAssert (a: assertion): C_stm S_SAssert
| C_SSkip: C_stm S_SSkip
| C_SSeq (s1 s2: S_stm) (c1: C_stm s1) (c2: C_stm s2): C_stm (S_SSeq s1 s2).

Parameter S_res: Type.

Parameter C_res: S_res -> Type.

Parameter S_split: S_stm -> S_res.

Parameter res_assert: assertion -> C_res (S_split S_SAssert).
Parameter res_skip: C_res (S_split S_SSkip).
Parameter res_seq: forall s1 s2, C_res (S_split s1) -> C_res (S_split s2) -> C_stm s1 -> C_stm s2 -> C_res (S_split (S_SSeq s1 s2)).


Fixpoint C_split (s: S_stm) (c: C_stm s): C_res (S_split s) :=
  match c as c0 in C_stm s0
    return C_res (S_split s0)
  with
  | C_SAssert a => res_assert a
  | C_SSkip => res_skip
  | C_SSeq s1 s2 c1 c2 => res_seq s1 s2 (C_split s1 c1) (C_split s2 c2) c1 c2
  end.