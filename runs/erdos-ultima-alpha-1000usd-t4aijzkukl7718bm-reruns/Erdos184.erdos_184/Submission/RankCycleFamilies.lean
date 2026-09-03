import Submission.RankCriticalPartitions

/-!
Rank constraints on the cycle families in a rank-critical graph. These are
necessary conditions only. In particular, no independent-transversal theorem
or uniformly bounded absorption theorem is assumed or proved here.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.RankCycleFamilies
open RankCritical RankCriticalCuts RankCriticalPartitions

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Removing the complementary pieces of an edge partition retains exactly
the edge union of the chosen subfamily. -/
lemma residual_complement_union (D S : Finset G.Subgraph)
    (hd : IsDecomposition G D) (hSD : S ⊆ D) :
    G \ unionPieces G (D \ S) = unionPieces G S := by
  apply SimpleGraph.edgeSet_injective
  ext e
  rw [edgeSet_sdiff, unionPieces_edgeSet, unionPieces_edgeSet]
  constructor
  · rintro ⟨he, hn⟩
    rw [← hd.2] at he
    obtain ⟨H, hHD, heH⟩ := Set.mem_iUnion₂.mp he
    have hHS : H ∈ S := by
      by_contra h
      exact hn (Set.mem_iUnion₂.mpr ⟨H, Finset.mem_sdiff.mpr ⟨hHD,h⟩,heH⟩)
    exact Set.mem_iUnion₂.mpr ⟨H,hHS,heH⟩
  · intro he
    obtain ⟨H,hHS,heH⟩ := Set.mem_iUnion₂.mp he
    refine ⟨SimpleGraph.edgeSet_mono H.spanningCoe_le heH, ?_⟩
    intro hbad
    obtain ⟨K,hKP,heK⟩ := Set.mem_iUnion₂.mp hbad
    obtain ⟨hKD,hKS⟩ := Finset.mem_sdiff.mp hKP
    have hne : H ≠ K := fun h => hKS (h ▸ hHS)
    exact Set.disjoint_left.mp (hd.1 (hSD hHS) hKD hne) heH heK

/-- An optimal critical family has one more piece than the C-rank budget,
but every proper subfamily satisfies that budget on its own edge union. -/
theorem proper_subfamily_rank_bound {C : ℕ} (hG : IsCritical C G)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (hsize : D.card = C * graphRank G + 1)
    (S : Finset G.Subgraph) (hSD : S ⊆ D) (hne : S ≠ D) :
    S.card ≤ C * graphRank (unionPieces G S) := by
  have hp : (D \ S).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hDS : D ⊆ S := Finset.sdiff_eq_empty_iff_subset.mp he
    exact hne (Finset.Subset.antisymm hSD hDS)
  have hb := hG.packing_cost (D \ S) hp
    (fun H hH => hc H (Finset.mem_sdiff.mp hH).1)
    (fun H hH K hK hHK => hd.1 (Finset.mem_sdiff.mp hH).1
      (Finset.mem_sdiff.mp hK).1 hHK)
  rw [residual_complement_union D S hd hSD, Finset.card_sdiff_of_subset hSD] at hb
  have hcard := Finset.card_le_card hSD
  omega

/-- The rank-transversal inequalities hold after reserving any one specified
piece of an optimal critical decomposition. This does not itself choose
representative edges or prove that their union is a forest. -/
lemma reserved_subfamily_rank_bound {C : ℕ} (hG : IsCritical C G)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (hsize : D.card = C * graphRank G + 1)
    (H₀ : G.Subgraph) (hH₀ : H₀ ∈ D) :
    ∀ S ⊆ D.erase H₀, S.card ≤ C * graphRank (unionPieces G S) := by
  intro S hS
  apply proper_subfamily_rank_bound hG D hc hd hsize S
    (hS.trans (Finset.erase_subset H₀ D))
  intro h
  have hm := hS (h.symm ▸ hH₀)
  exact (Finset.mem_erase.mp hm).1 rfl

/-- Any nontrivial vertex partition must be crossed by more than C times
its rank loss MANY DISTINCT PIECES, in every decomposition. -/
theorem partition_crossing_pieces_lower {I : Type*} [Fintype I]
    {C : ℕ} (hG : IsCritical C G) (hconn : G.Connected)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (f : V → I) (hf : Function.Surjective f) (hk : 2 ≤ Fintype.card I) :
    C * (Fintype.card I - 1) < (crossingPieces D (monochromatic G f)).card := by
  let R := monochromatic G f
  let P := crossingPieces D R
  have hres : G \ unionPieces G P ≤ R := crossingPieces_residual_le G R D hd
  have hpart := component_card_ge_colors G f hf
  have hcomp := component_card_le R
  have hnr : graphRank R + Fintype.card I ≤ Fintype.card V := by
    unfold graphRank
    change Fintype.card I ≤ Nat.card R.ConnectedComponent at hpart
    omega
  have hng := connected_rank hconn
  have hneR : R ≠ G := by
    intro h
    rw [h] at hnr
    omega
  have hp : P.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hGR : G ≤ R := by simpa [he,unionPieces] using hres
    exact hneR (le_antisymm (monochromatic_le G f) hGR)
  have hcost := hG.packing_cost P hp
    (fun H hH => hc H (Finset.mem_filter.mp hH).1)
    (fun H hH K hK hne => hd.1 (Finset.mem_filter.mp hH).1
      (Finset.mem_filter.mp hK).1 hne)
  have hr := Nat.mul_le_mul_left C (rank_mono hres)
  have hgap : graphRank R + (Fintype.card I - 1) ≤ graphRank G := by omega
  have hmul := Nat.mul_le_mul_left C hgap
  rw [Nat.mul_add] at hmul
  change C * (Fintype.card I - 1) < P.card
  omega

/-- Reserving any one cycle still leaves the non-strict C-fold partition
inequalities on the remaining crossing pieces. -/
lemma reserved_partition_crossing_pieces {I : Type*} [Fintype I]
    {C : ℕ} (hG : IsCritical C G) (hconn : G.Connected)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (H₀ : G.Subgraph)
    (f : V → I) (hf : Function.Surjective f) (hk : 2 ≤ Fintype.card I) :
    C * (Fintype.card I - 1) ≤
      ((crossingPieces D (monochromatic G f)).erase H₀).card := by
  have hb := partition_crossing_pieces_lower hG hconn D hc hd f hf hk
  by_cases hm : H₀ ∈ crossingPieces D (monochromatic G f)
  · have hh := Finset.card_erase_add_one hm
    omega
  · simpa [hm] using hb.le

end Erdos184.RankCycleFamilies
