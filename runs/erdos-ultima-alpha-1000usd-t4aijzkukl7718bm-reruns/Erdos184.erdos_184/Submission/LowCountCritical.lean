import Submission.SmallSlackExact
import Submission.InvariantHajos
import Submission.DegreeTightOptimal

/-! Count-critical graphs with minimum cycle count at most two are invariant.
This is a restricted result; no bound on the count of an arbitrary critical
graph is assumed or proved. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.LowCountCritical
open CountCritical CycleNumberSubmodularity FractionalCycles FractionalEnvelope
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
attribute [local instance] FractionalCycles.cyclePieceFintype

omit [Fintype V] in
lemma unionPieces_eq_of_decomposition (D : Finset G.Subgraph)
    (hd : IsDecomposition G D) : unionPieces G D = G := by
  apply edgeSet_injective
  rw [unionPieces_edgeSet]
  exact hd.2

/-- An even graph of minimum cycle count at most two is fractionally exact.
It need not itself be count-critical or have invariant partition count. -/
lemma optimum_eq_number_of_number_le_two (he : ∀ v, Even (G.degree v))
    (hk : cycleNumber G ≤ 2) : optimum G = (cycleNumber G : ℝ) := by
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists G he
  have hh := SmallSlackExact.at_most_two_exact D hc hd.1 (by omega)
  rwa [unionPieces_eq_of_decomposition D hd,hcard] at hh

/-- At counts zero, one and two the graphic fractional exactness result
makes count-criticality strong enough to force invariance. -/
lemma invariant_of_count_le_two {k : ℕ} (hG : IsCountCritical k G) (hk : k ≤ 2) :
    InvariantPartitions.HasInvariantCount G := by
  apply invariant_of_countCritical_fractionalExact G k hG
  intro t ht
  have heq := optimum_eq_number_of_number_le_two hG.1 (by simpa [hG.2.1] using hk)
  have hb := optimum_le_cost ht
  rw [heq,hG.2.1] at hb
  exact hb

lemma exists_degree_two_of_count_le_two {k : ℕ}
    (hG : IsCountCritical k G) (hk : k ≤ 2) (hne : G ≠ ⊥) :
    ∃ v, G.degree v = 2 :=
  (invariant_of_count_le_two hG hk).exists_degree_two hG.1 hne

/-- If a critical graph has no degree-two vertex, all its degrees lie
strictly below twice its minimum count. This uses optimal extendability,
not any inheritance of criticality by the whole residual. -/
lemma degree_add_two_le_twice_count {k : ℕ} (hG : IsCountCritical k G)
    (hne : G ≠ ⊥) (hno : ∀ v, G.degree v ≠ 2) (v : V) :
    G.degree v + 2 ≤ 2 * k := by
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists G hG.1
  have hh := DegreeTightOptimal.strict_degree_slack hG.1 hne hG.allCyclesOptimal hno
    D hc hd v
  rwa [hcard,hG.2.1] at hh

/-- The next count has a weaker bound: a nonempty critical graph of count
at most three has a supported vertex of degree at most four. -/
lemma exists_positive_degree_le_four_of_count_le_three {k : ℕ}
    (hG : IsCountCritical k G) (hk : k ≤ 3) (hne : G ≠ ⊥) :
    ∃ v ∈ G.support, G.degree v ≤ 4 := by
  by_cases htwo : ∃ v, G.degree v = 2
  · obtain ⟨v,hv⟩ := htwo
    refine ⟨v,(G.degree_pos_iff_mem_support v).mp (by omega),by omega⟩
  · obtain ⟨v,w,hvw⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
    have hh := degree_add_two_le_twice_count hG hne (by simpa using htwo) v
    exact ⟨v,⟨w,hvw⟩,by omega⟩

/-- A degree-two-free critical graph of count at most three is four-regular
on its support. No nonexistence theorem for this case is asserted. -/
lemma supported_degree_eq_four_of_count_le_three {k : ℕ}
    (hG : IsCountCritical k G) (hk : k ≤ 3) (hne : G ≠ ⊥)
    (hno : ∀ v, G.degree v ≠ 2) (v : V) (hv : v ∈ G.support) :
    G.degree v = 4 := by
  have hh := degree_add_two_le_twice_count hG hne hno v
  have hp := (G.degree_pos_iff_mem_support v).mpr hv
  have hn := hno v
  obtain ⟨r,hr⟩ := hG.1 v
  omega

end Erdos184.LowCountCritical
