import Submission.FractionalAveraging

/-!
A precise conditional reduction to multiplicative fractional comparison on
fixed-count-critical graphs. The comparison hypothesis remains unproved.
Fractional cost is never assumed monotone under passage to an even subgraph.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.CountCritical
open CycleNumberSubmodularity FractionalCycles
variable {V : Type*} [Fintype V]
attribute [local instance] FractionalCycles.cyclePieceFintype
set_option maxHeartbeats 1000000

/-- A bound valid for critical even subgraphs, on the SAME ambient vertex
type, bounds the minimum count of the original even graph. -/
lemma bound_of_critical_subgraph_bound (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ H : SimpleGraph V, H ≤ G → ∀ k : ℕ, IsCountCritical k H → (k : ℝ) ≤ B) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ (D.card : ℝ) ≤ B := by
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists G he
  refine ⟨D,hc,hd,?_⟩
  rw [hcard]
  by_cases hk : cycleNumber G = 0
  · simpa [hk] using hB
  · obtain ⟨H,hHG,hH⟩ := extract G he (cycleNumber G) (Nat.pos_of_ne_zero hk) le_rfl
    exact hb H hHG (cycleNumber G) hH

/-- Restricted fractional comparison suffices. The fractional solution is
constructed anew on the extracted kernel; it is NOT restricted from G. -/
lemma bound_of_critical_fractional_comparison (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (K : ℝ) (hK : 0 ≤ K)
    (hcomp : ∀ H : SimpleGraph V, H ≤ G → ∀ k : ℕ, IsCountCritical k H →
      ∀ t : CyclePiece H → ℝ, IsFractionalPartition H t → (k : ℝ) ≤ K * ∑ J, t J) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ (D.card : ℝ) ≤ (2*K) * Fintype.card V := by
  apply bound_of_critical_subgraph_bound G he ((2*K) * Fintype.card V) (by positivity)
  intro H hHG k hH
  obtain ⟨t,ht,hcost⟩ := exists_fractional_partition_linear H hH.1
  have hlow := hcomp H hHG k hH t ht
  have hupp := mul_le_mul_of_nonneg_left hcost hK
  nlinarith

universe u
/-- A fixed multiplicative comparison for count-critical graphs would settle
the original conjecture. This is a conditional theorem, not such a comparison. -/
lemma conjecture_of_critical_fractional_comparison (K : ℝ) (hK : 0 ≤ K)
    (hcomp : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (k : ℕ),
      IsCountCritical k G → ∀ t : CyclePiece G → ℝ,
        IsFractionalPartition G t → (k : ℝ) ≤ K * ∑ J, t J) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_bound.mpr
  refine ⟨2*K,?_⟩
  intro V _ _ G he
  obtain ⟨D,hc,hd,hcost⟩ := bound_of_critical_fractional_comparison G he K hK
    (fun H _ k hH t ht => hcomp H k hH t ht)
  refine ⟨D,?_,hd,hcost⟩
  intro H hH
  apply Or.inl
  refine ⟨(hc H hH).1,?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hc H hH).2 v

end Erdos184.CountCritical
