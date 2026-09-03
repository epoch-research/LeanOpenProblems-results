import Submission.Infrastructure

/-!
# Checks for the Erdős 184 infrastructure

The type-only check below uses `type_of%` to read the original statement, not its
admitted proof.  Its axiom report verifies this distinction.  No result here or
in `Infrastructure.lean` proves the uniform linear-bound hypothesis.
-/

open Filter SimpleGraph

namespace Erdos184.Infrastructure.Audit

universe u

open scoped Classical in
/-- The reduction's conclusion is exactly the original target, universe-polymorphically. -/
theorem uniformBound_exactTarget (K : ℝ)
    (hK : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ K * (Fintype.card V : ℝ)) :
    type_of% @Erdos184.erdos_184.{u} := by
  exact asymptotic_of_uniform_linear_bound K hK

end Erdos184.Infrastructure.Audit

#print axioms Erdos184.Infrastructure.singleEdgeSubgraph
#print axioms Erdos184.Infrastructure.singleEdgeSubgraph_edgeSet
#print axioms Erdos184.Infrastructure.singleEdgeSubgraph_injective
#print axioms Erdos184.Infrastructure.coe_edgeFinset_card
#print axioms Erdos184.Infrastructure.singleEdgeSubgraph_coe_edgeFinset_card
#print axioms Erdos184.Infrastructure.singleEdgeSubgraph_isCycleOrEdge
#print axioms Erdos184.Infrastructure.singletonEdgeDecomposition
#print axioms Erdos184.Infrastructure.mem_singletonEdgeDecomposition
#print axioms Erdos184.Infrastructure.singletonEdgeDecomposition_single_edge
#print axioms Erdos184.Infrastructure.singletonEdgeDecomposition_isCycleOrEdge
#print axioms Erdos184.Infrastructure.singletonEdgeDecomposition_isDecomposition
#print axioms Erdos184.Infrastructure.singletonEdgeDecomposition_card
#print axioms Erdos184.Infrastructure.singletonEdgeDecomposition_card_le
#print axioms Erdos184.Infrastructure.exists_singleton_edge_decomposition
#print axioms Erdos184.Infrastructure.isCycleOrEdge_toSubgraph_of_isCycle
#print axioms Erdos184.Infrastructure.asymptotic_of_uniform_linear_bound
#print axioms Erdos184.Infrastructure.Audit.uniformBound_exactTarget

#check @Erdos184.Infrastructure.exists_singleton_edge_decomposition
#check @Erdos184.Infrastructure.isCycleOrEdge_toSubgraph_of_isCycle
#check @Erdos184.Infrastructure.asymptotic_of_uniform_linear_bound
#check @Erdos184.Infrastructure.Audit.uniformBound_exactTarget
