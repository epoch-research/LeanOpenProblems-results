import Submission.StarCutBudget

/-! A cut bounds the degree removed at a vertex by any prescribed-root cycle packing. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.StarCutBudget
open StarElimination RankCriticalCuts RankCriticalPartitions
variable {V I : Type*} [Fintype V] {G : SimpleGraph V}

lemma packing_star_degree (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet)) (w : V) :
    2 * (star P w).card = (unionPieces G P).degree w := by
  rw [unionPieces_degree G P hd]
  unfold StarElimination.star
  rw [Finset.card_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H hH
  by_cases hw : w ∈ H.verts
  · have hh := (hc H hH).2 ⟨w,hw⟩
    rw [Subgraph.coe_degree] at hh
    have he : H.degree w = 2 := by
      simpa only [Subgraph.degree,← Nat.card_eq_fintype_card] using hh
    simp [hw,he]
  · simp [hw,Subgraph.degree_of_notMem_verts hw]

lemma packing_degree_le_cut (he : ∀ v, Even (G.degree v))
    (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    {v w : V} (hv : ∀ H ∈ P, v ∈ H.verts)
    (f : V → I) (hne : f v ≠ f w) :
    (unionPieces G P).degree w ≤ (G.edgeSet \ (monochromatic G f).edgeSet).ncard := by
  obtain ⟨D,hcD,hdD,hPD⟩ := extend_packing he P hc hd
  have hs : star P w ⊆ crossingPieces D (monochromatic G f) := by
    intro H hH
    obtain ⟨hHP,hwH⟩ := (mem_star P w H).mp hH
    exact Finset.mem_filter.mpr ⟨hPD hHP,
      crossing_of_distinct_colors H (hc H hHP).1 f (hv H hHP) hwH hne⟩
  have hcount := Finset.card_le_card hs
  have hbudget := crossingPieces_budget G (monochromatic G f)
    (monochromatic_closed G f) D hcD hdD
  have hdegree := packing_star_degree P hc hd w
  omega

end Erdos184.StarCutBudget
