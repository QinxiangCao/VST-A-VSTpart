Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Export RamifyCoq.floyd_ext.closed_lemmas.
Require Import cprogs.unionfind_prog.
Require Export RamifyCoq.graph.graph_model.
Require Export RamifyCoq.graph.path_lemmas.
Require Export RamifyCoq.graph.subgraph2.
Require Export RamifyCoq.graph.graph_relation.
Require Export RamifyCoq.graph.reachable_computable.
Require Export RamifyCoq.msl_application.Graph.
Require Export RamifyCoq.msl_application.UnionFindGraph.
Require Export RamifyCoq.msl_application.GList.
Require Export RamifyCoq.msl_application.GList_UnionFind.
Require Export RamifyCoq.floyd_ext.share.
Require Export RamifyCoq.sample_mark.spatial_graph_glist.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Global Existing Instance CompSpecs.

Definition node_type := Tstruct _Node noattr.

Coercion UGraph_LGraph: Graph >-> LGraph.
Coercion LGraph_SGraph: LGraph >-> SGraph.
Identity Coercion ULGraph_LGraph: LGraph >-> UnionFindGraph.LGraph.
Identity Coercion LGraph_LabeledGraph: UnionFindGraph.LGraph >-> LabeledGraph.
Identity Coercion SGraph_PointwiseGraph: SGraph >-> PointwiseGraph.
Coercion pg_lg: LabeledGraph >-> PreGraph.

Notation vertices_at sh P g:= (@vertices_at _ _ _ _ _ mpred (@SGP pSGG_VST nat unit (sSGG_VST sh)) (SGA_VST sh) P g).
Notation whole_graph sh g := (vertices_at sh (vvalid g) g).
Notation graph sh x g := (@reachable_vertices_at _ _ _ _ _ _ _ _ _ _ (@SGP pSGG_VST nat unit (sSGG_VST sh)) _ x g).
Notation Graph := (@Graph pSGG_VST).
Existing Instances maGraph finGraph liGraph RGF.

Definition vlabel_in_bound (g: Graph) := forall x, vvalid g x -> Int.min_signed <= Z.of_nat (vlabel g x) <= Int.max_signed.

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH sh: wshare, n:Z
  PRE [ 67%positive OF tint]
     PROP (0 <= n <= Int.max_signed)
     LOCAL (temp 67%positive (Vint (Int.repr n)))
     SEP ()
  POST [ tptr tvoid ]
     EX v: addr,
     PROP ()
     LOCAL (temp ret_temp (pointer_val_val v))
     SEP (data_at sh node_type (pointer_val_val null, (Vint (Int.repr 0)))
              (pointer_val_val v)).

Lemma pointer_val_val_is_pointer_or_null: forall x,
  is_pointer_or_null (pointer_val_val x).
Proof.
  intros.
  destruct x; simpl; auto.
Qed.

Hint Resolve pointer_val_val_is_pointer_or_null.
