import Submission.StarElimination
import Submission.RankCriticalPartitions

/-!
A necessary cut condition for vertices eliminated by a prescribed cycle star.
This does not assert existence of an efficiently eliminating star.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.StarCutBudget
open StarElimination RankCriticalCuts RankCriticalPartitions
variable {V I : Type*} [Fintype V] {G : SimpleGraph V}

lemma crossing_of_distinct_colors (H : G.Subgraph) (hc : H.coe.Connected)
    (f : V → I) {v w : V} (hv : v ∈ H.verts) (hw : w ∈ H.verts)
    (hne : f v ≠ f w) : (H.edgeSet \ (monochromatic G f).edgeSet).Nonempty := by
  by_contra hn
  have hsub : H.edgeSet ⊆ (monochromatic G f).edgeSet := by
    intro e he
    by_contra he'
    exact hn ⟨e,he,he'⟩
  let φ : H.coe →g monochromatic G f := {
    toFun := Subtype.val
    map_rel' := fun {a b} h => hsub (show s(a.val,b.val) ∈ H.edgeSet from h) }
  exact hne (color_eq_of_reachable G f ((hc.preconnected ⟨v,hv⟩ ⟨w,hw⟩).map φ))

/-- If the star at w is contained in the star at v, every cut separating
v from w has at least degree(w) edges. -/
lemma degree_le_cut_of_star_subset (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) {v w : V} (hsub : star D w ⊆ star D v)
    (f : V → I) (hne : f v ≠ f w) :
    G.degree w ≤ (G.edgeSet \ (monochromatic G f).edgeSet).ncard := by
  have hs : star D w ⊆ crossingPieces D (monochromatic G f) := by
    intro H hH
    have hw := (mem_star D w H).mp hH
    have hv := (mem_star D v H).mp (hsub hH)
    exact Finset.mem_filter.mpr ⟨hw.1,
      crossing_of_distinct_colors H (hc H hw.1).1 f hv.2 hw.2 hne⟩
  have hcard := Finset.card_le_card hs
  have hbudget := crossingPieces_budget G (monochromatic G f)
    (monochromatic_closed G f) D hc hd
  have hdegree := star_card D hc hd w
  omega

lemma degree_le_cut_of_dominated (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) {v w : V} (hw : w ∈ dominated D v)
    (f : V → I) (hne : f v ≠ f w) :
    G.degree w ≤ (G.edgeSet \ (monochromatic G f).edgeSet).ncard := by
  have hh := (Finset.mem_filter.mp hw).2
  exact degree_le_cut_of_star_subset D hc hd hh.2 f hne

/-- An arbitrary cycle packing can be retained in a full partition of an
even graph. No optimality claim is made. -/
lemma extend_packing (he : ∀ v, Even (G.degree v)) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet)) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ P ⊆ D := by
  have hr := even_residual_of_cycle_packing G he P hc hd
  obtain ⟨E,hcE,hdE⟩ := even_cycle_decomposition (G \ unionPieces G P) (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hr v)
  obtain ⟨D,hcD,hdD,hPD,_⟩ := complete_cycle_packing_extension G P hc hd E (by
    intro H hH
    simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hcE H hH) hdE
  exact ⟨D,hcD,hdD,hPD⟩

/-- Every vertex exhausted by a packing through v obeys the same cut
condition, whether or not v itself has been exhausted. -/
lemma degree_le_cut_of_isolated (he : ∀ v, Even (G.degree v))
    (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    {v w : V} (hv : ∀ H ∈ P, v ∈ H.verts)
    (hw : w ∉ (G \ unionPieces G P).support)
    (f : V → I) (hne : f v ≠ f w) :
    G.degree w ≤ (G.edgeSet \ (monochromatic G f).edgeSet).ncard := by
  obtain ⟨D,hcD,hdD,hPD⟩ := extend_packing he P hc hd
  have hs := (isolated_iff_star_subset D P hPD hcD hdD w).mp hw
  apply degree_le_cut_of_star_subset D hcD hdD (v := v) (w := w) ?_ f hne
  intro H hH
  have hHP := hs hH
  exact (mem_star D v H).mpr ⟨hPD hHP,hv H hHP⟩

lemma packing_eq_star_of_exhausted (D P : Finset G.Subgraph) (hPD : P ⊆ D)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) {v : V} (hv : ∀ H ∈ P, v ∈ H.verts)
    (hi : v ∉ (G \ unionPieces G P).support) : P = star D v := by
  apply Finset.Subset.antisymm
  · intro H hH
    exact (mem_star D v H).mpr ⟨hPD hH,hv H hH⟩
  · exact (isolated_iff_star_subset D P hPD hc hd v).mp hi

lemma card_of_exhausted (he : ∀ v, Even (G.degree v))
    (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    {v : V} (hv : ∀ H ∈ P, v ∈ H.verts)
    (hi : v ∉ (G \ unionPieces G P).support) : 2 * P.card = G.degree v := by
  obtain ⟨D,hcD,hdD,hPD⟩ := extend_packing he P hc hd
  rw [packing_eq_star_of_exhausted D P hPD hcD hdD hv hi]
  exact star_card D hcD hdD v

end Erdos184.StarCutBudget
