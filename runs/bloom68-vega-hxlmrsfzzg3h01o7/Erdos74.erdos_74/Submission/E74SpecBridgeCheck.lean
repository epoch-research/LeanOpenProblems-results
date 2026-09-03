import Submission.E74SpecBridge

/-! Signature, application, and axiom audit for the specification bridge. -/

#print axioms E74.edgeSet_finite_of_verts_finite
#print axioms E74.isBipartite_delete_all_edges
#print axioms E74.edgeDistancesToBipartite_nonempty
#print axioms E74.minEdgeDistToBipartite_attained
#print axioms E74.subgraph_edgeSet_ncard_le_choose
#print axioms E74.minEdgeDistToBipartite_le_choose
#print axioms E74.subgraphEdgeDistsToBipartite_bddAbove
#print axioms E74.minEdgeDistToBipartite_le_max
#print axioms E74.edgeDeletionBudget
#print axioms E74.exists_boolCut_of_deleteEdges_isBipartite
#print axioms E74.coeSubgraph_cut_of_deleteEdges_isBipartite
#print axioms E74.smallCuts_of_maxSubgraphEdgeDistToBipartite

#check E74.edgeSet_finite_of_verts_finite
#check E74.isBipartite_delete_all_edges
#check E74.edgeDistancesToBipartite_nonempty
#check E74.minEdgeDistToBipartite_attained
#check E74.subgraph_edgeSet_ncard_le_choose
#check E74.minEdgeDistToBipartite_le_choose
#check E74.subgraphEdgeDistsToBipartite_bddAbove
#check E74.minEdgeDistToBipartite_le_max
#check E74.edgeDeletionBudget
#check E74.exists_boolCut_of_deleteEdges_isBipartite
#check E74.coeSubgraph_cut_of_deleteEdges_isBipartite
#check E74.smallCuts_of_maxSubgraphEdgeDistToBipartite

universe u

/-- Verify application after installing the finite vertex instance, with an arbitrary ambient type. -/
example {V : Type u} (B f : ℕ → ℕ)
    (hf : ∀ k, 2 ≤ k → ∀ n, n ≤ B k → f n < k)
    (G : SimpleGraph V)
    (hG : ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n)
    (A : G.Subgraph) (hA : A.verts.Finite) :
    letI := hA.fintype
    E74.SmallCuts A.coe B := by
  letI := hA.fintype
  exact E74.smallCuts_of_maxSubgraphEdgeDistToBipartite B f hf G hG A hA

/-- Verify the expanded hereditary conclusion, including the cut on all of `A.verts`. -/
example {V : Type u} (B f : ℕ → ℕ)
    (hf : ∀ k, 2 ≤ k → ∀ n, n ≤ B k → f n < k)
    (G : SimpleGraph V)
    (hG : ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n)
    (A : G.Subgraph) (hA : A.verts.Finite) :
    letI := hA.fintype
    ∀ k, 2 ≤ k → ∀ H : A.coe.Subgraph, H.verts.ncard ≤ B k →
      ∃ p : A.verts → Bool, (E74.badEdges H.spanningCoe p).card < k := by
  exact E74.smallCuts_of_maxSubgraphEdgeDistToBipartite B f hf G hG A hA
