import Submission.InvariantLowDegree
import Submission.BlockPotentialPlateau

/-!
Block-rank descent and a sharper count bound in the invariant-count class.
No implication from count-criticality to invariance is asserted.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.InvariantPartitions
open BlockRankPotential CycleNumberSubmodularity

variable {V : Type*} [Fintype V]

/-- The hereditary two-vertex intersection restriction supplies genuine
critical-kernel descent. The smaller kernel is extracted after the deletion,
rather than identifying it with the whole residual. -/
lemma criticalDescent_of_intersection_le_two (G : SimpleGraph V)
    (hi : ∀ H K : G.Subgraph,
      (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      (K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) →
      Disjoint H.edgeSet K.edgeSet → (H.verts ∩ K.verts).ncard ≤ 2) :
    CriticalDescent G := by
  apply criticalDescent_of_cycle_descent G
  intro H hHG k hk hcH
  have hne : H ≠ ⊥ := by
    intro h
    have hh := hcH.2.1
    rw [h,CountCritical.number_bot] at hh
    omega
  obtain ⟨v,hv⟩ := exists_degree_two_of_intersection_le_two H hcH.1 hne
    (intersection_le_two_of_le hHG hi)
  exact exists_cycle_drop_of_degree_two hcH.1 v hv

lemma HasInvariantCount.criticalDescent {G : SimpleGraph V}
    (hi : HasInvariantCount G) (he : ∀ v, Even (G.degree v)) :
    CriticalDescent G :=
  criticalDescent_of_intersection_le_two G (hi.intersection_le_two he)

/-- The block potential bounds the minimum whenever the critical descent
hypothesis is available. This general helper retains that hypothesis. -/
lemma number_le_potential_of_descent (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hd : CriticalDescent G) :
    (cycleNumber G : ℤ) ≤ potential G := by
  by_cases hk : cycleNumber G = 0
  · simpa only [hk,Nat.cast_zero] using potential_nonneg G
  obtain ⟨H,hHG,hH⟩ := CountCritical.extract G he (cycleNumber G)
    (Nat.pos_of_ne_zero hk) le_rfl
  exact (critical_bound_of_descent G hd _ H hHG hH).trans (potential_mono hHG)

lemma number_le_potential_of_intersection_le_two (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v))
    (hi : ∀ H K : G.Subgraph,
      (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      (K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) →
      Disjoint H.edgeSet K.edgeSet → (H.verts ∩ K.verts).ncard ≤ 2) :
    (cycleNumber G : ℤ) ≤ potential G :=
  number_le_potential_of_descent G he (criticalDescent_of_intersection_le_two G hi)

lemma HasInvariantCount.number_le_potential {G : SimpleGraph V}
    (hi : HasInvariantCount G) (he : ∀ v, Even (G.degree v)) :
    (cycleNumber G : ℤ) ≤ potential G :=
  number_le_potential_of_descent G he (hi.criticalDescent he)

lemma HasInvariantCount.decomposition_card_le_potential {G : SimpleGraph V}
    (hi : HasInvariantCount G) (he : ∀ v, Even (G.degree v))
    (D : Finset G.Subgraph)
    (hcD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdD : IsDecomposition G D) : (D.card : ℤ) ≤ potential G := by
  obtain ⟨E,hcE,hdE,hE⟩ := CountCritical.minimum_exists G he
  have hh := hi D E hcD hdD hcE hdE
  rw [hh,hE]
  exact hi.number_le_potential he

lemma HasInvariantCount.decomposition_card_le_order_sub_two {G : SimpleGraph V}
    (hi : HasInvariantCount G) (he : ∀ v, Even (G.degree v))
    (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (hcut : ∀ v a b, a ≠ v → b ≠ v → (G.deleteIncidenceSet v).Reachable a b)
    (D : Finset G.Subgraph)
    (hcD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdD : IsDecomposition G D) : D.card + 2 ≤ Fintype.card V := by
  have hh := hi.decomposition_card_le_potential he D hcD hdD
  rw [potential_of_no_cut hG hn hcut] at hh
  omega

/-- Nonempty invariant graphs satisfy the support-minus-two bound even
without connectedness or a no-cut-vertex assumption. -/
lemma HasInvariantCount.decomposition_card_le_support_sub_two {G : SimpleGraph V}
    (hi : HasInvariantCount G) (he : ∀ v, Even (G.degree v)) (hne : G ≠ ⊥)
    (D : Finset G.Subgraph)
    (hcD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdD : IsDecomposition G D) : D.card + 2 ≤ G.support.ncard := by
  have hc := hi.decomposition_card_le_potential he D hcD hdD
  have hp := potential_le_twice_rank_sub_support G
  have hr := RankBlocks.rank_le_support_sub_one G hne
  have hs := support_card_two_le G hne
  omega

/-- A genuine descending critical kernel in the invariant class. It is
not asserted that the entire cycle-deleted residual is critical. -/
lemma HasInvariantCount.critical_kernel_step {G : SimpleGraph V} {k : ℕ}
    (hi : HasInvariantCount G) (hc : CountCritical.IsCountCritical k G)
    (hk : 0 < k) :
    ∃ K : SimpleGraph V, K ≤ G ∧ CountCritical.IsCountCritical (k-1) K ∧
      HasInvariantCount K ∧ potential K + 1 ≤ potential G := by
  obtain ⟨K,hKG,hK,hstep⟩ := hi.criticalDescent hc.1 G le_rfl k hk hc
  exact ⟨K,hKG,hK,hi.of_le hc.1 hKG,hstep⟩

end Erdos184.InvariantPartitions
