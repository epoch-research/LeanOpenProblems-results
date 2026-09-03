import Submission.LongCyclePacking

/-!
A quantitative short-length tail bound for a minimum cycle decomposition.
The bound grows with the length threshold. It is not a uniform linear bound
on the entire decomposition.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.MinimumCycleTail

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Only O(n log L) members of a minimum cycle decomposition can have length
at most L. A maximal long-cycle packing absorbs half the candidate count. -/
theorem short_subfamily_card (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (S : Finset G.Subgraph) (hSD : S ⊆ D) (L t : ℕ)
    (hlen : ∀ H ∈ S, H.edgeSet.ncard ≤ L) (hpow : 2 * L ≤ 2 ^ t) :
    S.card ≤ (4 * t + 2) * Fintype.card V := by
  by_cases hs : S.Nonempty
  · have hL : 0 < L := by
      obtain ⟨H, hH⟩ := hs
      have hh := cycle_edgeSet_three_le H (hc H (hSD hH)).1 (hc H (hSD hH)).2
      have hl := hlen H hH
      omega
    have hdis : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet) :=
      fun H hH J hJ hne => hd.1 (hSD hH) (hSD hJ) hne
    let U := unionPieces G S
    have heU : ∀ v, Even (U.degree v) := by
      intro v
      change Even ((unionPieces G S).degree v)
      rw [unionPieces_degree G S hdis]
      exact Finset.even_sum _ (fun H hH =>
        regular_two_piece_degree_even H (hc H (hSD hH)).2 v)
    have hcount : U.edgeFinset.card ≤ L * S.card := by
      rw [unionPieces_edge_card G S hdis]
      calc
        (∑ H ∈ S, H.edgeSet.ncard) ≤ ∑ _ ∈ S, L :=
          Finset.sum_le_sum hlen
        _ = L * S.card := by simp [mul_comm]
    obtain ⟨P, hcP, hdP, heR, hr, hcost⟩ :=
      long_cycle_packing_phase U heU (2 * L + 1) (by omega)
    let R := U \ unionPieces U P
    have hr' : R.edgeFinset.card ≤ 2 ^ t * Fintype.card V := by
      calc
        R.edgeFinset.card ≤ (2 * L) * Fintype.card V := by
          simpa only [Nat.add_sub_cancel] using hr
        _ ≤ _ := Nat.mul_le_mul_right _ hpow
    obtain ⟨F, hcF, hdF, hf⟩ := even_cycle_decomposition_dyadic_bound R (by
      intro v
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heR v) t (by
      simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hr')
    have hp : 2 * P.card ≤ S.card := by
      have hprod : L * (2 * P.card) ≤ L * S.card := by
        nlinarith
      exact Nat.le_of_mul_le_mul_left hprod hL
    obtain ⟨E, hcE, hdE, hE⟩ := complete_cycle_packing U P hcP hdP F (by
      intro H hH
      refine ⟨(hcF H hH).1, ?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hcF H hH).2 v) hdF
    have hmin := subfamily_minimum_for_union G D hc hd hm S hSD E hcE hdE
    nlinarith
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

/-- The short-piece tail in a minimum decomposition, with an explicit dyadic
threshold. -/
lemma short_filter_card (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (L t : ℕ) (hpow : 2 * L ≤ 2 ^ t) :
    (D.filter (fun H => H.edgeSet.ncard ≤ L)).card ≤
      (4 * t + 2) * Fintype.card V :=
  short_subfamily_card D hc hd hm _ (Finset.filter_subset _ _) L t
    (fun H hH => (Finset.mem_filter.mp hH).2) hpow

/-- A large minimum partition forces many long cycles, and therefore many
edges. The subtracted short-piece allowance still depends on the threshold. -/
theorem edge_count_lower (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (L t : ℕ) (hpow : 2 * L ≤ 2 ^ t) :
    (L + 1) * (D.card - (4 * t + 2) * Fintype.card V) ≤ G.edgeFinset.card := by
  let S := D.filter (fun H => H.edgeSet.ncard ≤ L)
  let T := D \ S
  have hs : S ⊆ D := Finset.filter_subset _ _
  have hshort : S.card ≤ (4 * t + 2) * Fintype.card V :=
    short_filter_card D hc hd hm L t hpow
  have hcard : D.card - (4 * t + 2) * Fintype.card V ≤ T.card := by
    rw [Finset.card_sdiff_of_subset hs]
    omega
  have hlen : ∀ H ∈ T, L + 1 ≤ H.edgeSet.ncard := by
    intro H hH
    obtain ⟨hHD, hHS⟩ := Finset.mem_sdiff.mp hH
    have hn : ¬ H.edgeSet.ncard ≤ L := by
      intro hl
      exact hHS (Finset.mem_filter.mpr ⟨hHD, hl⟩)
    omega
  have hdis : Set.PairwiseDisjoint (T : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun H hH J hJ hne => hd.1 (Finset.mem_sdiff.mp hH).1 (Finset.mem_sdiff.mp hJ).1 hne
  have hpart := cycle_packing_edge_card_partition G T hdis
  calc
    (L + 1) * (D.card - (4 * t + 2) * Fintype.card V) ≤ (L + 1) * T.card :=
      Nat.mul_le_mul_left _ hcard
    _ = ∑ _ ∈ T, (L + 1) := by simp [mul_comm]
    _ ≤ ∑ H ∈ T, H.edgeSet.ncard := Finset.sum_le_sum hlen
    _ ≤ G.edgeFinset.card := by omega

end Erdos184.MinimumCycleTail
