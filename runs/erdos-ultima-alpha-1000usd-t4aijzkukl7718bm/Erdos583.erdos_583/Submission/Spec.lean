import FormalConjecturesUtil

/-! Erdős Problem 583. The conjecture below is not yet proved.
The previous development is preserved in SpecDevelopmentSnapshot.lean. -/

open SimpleGraph
namespace Erdos583

def IsPathSubgraph {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) : Prop :=
  ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ H = p.toSubgraph

def IsDecomposition {V : Type*} (G : SimpleGraph V) (D : Finset G.Subgraph) : Prop :=
  Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
  (⋃ H ∈ D, H.edgeSet) = G.edgeSet


theorem erdos_583 {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsPathSubgraph H) ∧
      IsDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ) / 2⌉₊ := by
  sorry

end Erdos583
