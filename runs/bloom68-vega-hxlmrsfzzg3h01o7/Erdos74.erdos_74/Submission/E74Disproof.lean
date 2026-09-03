import Submission.E74Transversal
import Submission.E74SpecBridge

open Filter SimpleGraph

namespace E74

universe u

/-- The explicit slowly divergent budget forces a three-coloring even on an
arbitrary infinite vertex type, by finite-subgraph compactness. -/
theorem colorable_three_of_budget {V : Type u} (G : SimpleGraph V)
    (hG : ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ budget n) :
    G.Colorable 3 := by
  classical
  apply SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom
  intro A hA
  letI := hA.fintype
  have hsmall : SmallCuts A.coe certificateBound :=
    smallCuts_of_maxSubgraphEdgeDistToBipartite certificateBound budget
      (fun k hk n hn => budget_lt (by omega) hn) G hG A hA
  exact (finite_colorable_three_of_smallCuts A.coe hsmall).some

/-- A sufficiently slow divergent budget is incompatible with infinite
chromatic number. -/
theorem disproof : ¬ (∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
      ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n) := by
  intro h
  obtain ⟨V, G, htop, hbudget⟩ := h budget budget_tendsto_atTop
  have hthree := colorable_three_of_budget G hbudget
  exact (SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr ⟨3, hthree⟩) htop

end E74

#print axioms E74.disproof
