import Submission.VertexSmoothing

/-!
Smoothing with both existing-edge and nonedge pairs. Existing-edge pairs
are restored by actual triangle cycles; no parallel edge is silently added.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184

lemma combine_pure_decompositions {V : Type*} [Fintype V] {G A B : SimpleGraph V}
    (hA : A ≤ G) (hB : B ≤ G)
    (hab : Disjoint A.edgeSet B.edgeSet) (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (DA : Finset A.Subgraph) (DB : Finset B.Subgraph)
    (hca : ∀ H ∈ DA, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) (hcb : ∀ H ∈ DB, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hda : IsDecomposition A DA) (hdb : IsDecomposition B DB) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧ IsDecomposition G D ∧ D.card ≤ DA.card + DB.card := by
  let D := DA.image (promote hA) ∪ DB.image (promote hB)
  refine ⟨D, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hH
      refine ⟨(hca K hK).1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hca K hK).2 v
    · obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hH
      refine ⟨(hcb K hK).1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcb K hK).2 v
  · intro H hH K hK hne
    rcases Finset.mem_union.mp hH with hH | hH <;>
      rcases Finset.mem_union.mp hK with hK | hK
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hK
      exact hda.1 hX hY (fun h => hne (congrArg (promote hA) h))
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hK
      exact hab.mono X.edgeSet_subset Y.edgeSet_subset
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hK
      exact hab.symm.mono X.edgeSet_subset Y.edgeSet_subset
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hK
      exact hdb.1 hX hY (fun h => hne (congrArg (promote hB) h))
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H, _, he⟩
      exact H.edgeSet_subset he
    · intro he
      rw [← hcover] at he
      rcases he with he | he
      · rw [← hda.2] at he
        simp only [Set.mem_iUnion] at he
        obtain ⟨H, hH, he⟩ := he
        exact ⟨promote hA H, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨H, hH, rfl⟩), he⟩
      · rw [← hdb.2] at he
        simp only [Set.mem_iUnion] at he
        obtain ⟨H, hH, he⟩ := he
        exact ⟨promote hB H, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨H, hH, rfl⟩), he⟩
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)


namespace MixedSmoothing
open MatchingSmoothing
variable {V : Type*}

lemma IsMatching.mono {M N : SimpleGraph V} (hm : IsMatching M) (hNM : N ≤ M) :
    IsMatching N := fun _ _ _ huv huw => hm (hNM huv) (hNM huw)

lemma fan_even [Fintype V] (M : SimpleGraph V) (hm : IsMatching M) :
    ∀ v, Even ((apex M M).degree v) := by
  intro v
  cases v with
  | none =>
    have h := degree_apex_new M M
    have hc := hm.support_card
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h ⊢
    rw [h,hc]
    exact even_two_mul _
  | some v =>
    have ha := degree_apex_old M M v
    have hmdeg := hm.degree_eq_indicator v
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at ha hmdeg ⊢
    rw [ha,hmdeg]
    exact ⟨_,rfl⟩

lemma fan_edge_card [Fintype V] (M : SimpleGraph V) (hm : IsMatching M) :
    (apex M M).edgeSet.ncard = 3 * M.edgeSet.ncard := by
  have hs := (apex M M).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_option] at hs
  have hnone := degree_apex_new M M
  have hsome : ∀ v, (apex M M).degree (some v) = 2 * M.degree v := by
    intro v
    have ha := degree_apex_old M M v
    have hb := hm.degree_eq_indicator v
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at ha hb ⊢
    omega
  have hM := M.sum_degrees_eq_twice_card_edges
  have hsup := hm.support_card
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
    edgeFinset_card] at hs hnone hsome hM
  simp_rw [hsome] at hs
  rw [← Finset.mul_sum,hnone] at hs
  simp only [Nat.card_coe_set_eq] at hs hM
  omega

/-- The matching fan decomposes into exactly one triangle per matching edge.
The proof obtains an even decomposition and forces its size by degree and
edge counting, without selecting arbitrary ordered endpoints for the edges. -/
lemma fan_decomposition [Fintype V] (M : SimpleGraph V) (hm : IsMatching M) :
    ∃ D : Finset (apex M M).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (apex M M) D ∧ D.card = M.edgeSet.ncard := by
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition (apex M M) (by
    intro v
    have hv := fan_even M hm v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hv)
  have hcD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    refine ⟨(hc H hH).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hc H hH).2 v
  refine ⟨D,hcD,hd,?_⟩
  have hlow := cycle_decomposition_vertex_count (apex M M) D hcD hd none
  have hf := Finset.card_filter_le D (fun H => none ∈ H.verts)
  have hdeg := degree_apex_new M M
  have hsup := hm.support_card
  have hup := cycle_decomposition_three_mul_card_le_edges (apex M M) D hcD hd
  have heq := fan_edge_card M hm
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
    edgeFinset_card] at hlow hdeg hup
  simp only [Nat.card_coe_set_eq] at hup
  omega

abbrev oldPairs (A M : SimpleGraph V) : SimpleGraph V := M ⊓ A
abbrev newPairs (A M : SimpleGraph V) : SimpleGraph V := M \ A
abbrev remaining (A M : SimpleGraph V) : SimpleGraph V := A \ M
abbrev toggled (A M : SimpleGraph V) : SimpleGraph V := remaining A M ⊔ newPairs A M

lemma support_split (A M : SimpleGraph V) :
    (newPairs A M).support ∪ (oldPairs A M).support = M.support := by
  ext v
  constructor
  · rintro (⟨u,hu⟩ | ⟨u,hu⟩) <;> exact ⟨u,hu.1⟩
  · rintro ⟨u,hu⟩
    by_cases hA : A.Adj v u
    · exact Or.inr ⟨u,hu,hA⟩
    · exact Or.inl ⟨u,hu,hA⟩

lemma split_support_disjoint (A M : SimpleGraph V) (hm : IsMatching M) :
    Disjoint (newPairs A M).support (oldPairs A M).support := by
  apply Set.disjoint_left.mpr
  rintro v ⟨u,hu⟩ ⟨w,hw⟩
  have heq := hm hu.1 hw.1
  exact hu.2 (heq.symm ▸ hw.2)

lemma pair_card_split [Fintype V] (A M : SimpleGraph V) :
    (newPairs A M).edgeSet.ncard + (oldPairs A M).edgeSet.ncard = M.edgeSet.ncard := by
  have hd : Disjoint (newPairs A M).edgeSet (oldPairs A M).edgeSet := by
    rw [edgeSet_sdiff,edgeSet_inf]
    exact Set.disjoint_sdiff_left.mono_right Set.inter_subset_right
  have heq : (newPairs A M).edgeSet ∪ (oldPairs A M).edgeSet = M.edgeSet := by
    rw [edgeSet_sdiff,edgeSet_inf]
    ext e
    simp only [Set.mem_union,Set.mem_diff,Set.mem_inter_iff]
    tauto
  rw [← Set.ncard_union_eq hd,heq]

lemma core_le (A M : SimpleGraph V) : apex (remaining A M) (newPairs A M) ≤ apex A M := by
  intro x y h
  cases x <;> cases y
  · exact h.elim
  · exact SimpleGraph.support_mono sdiff_le h
  · exact SimpleGraph.support_mono sdiff_le h
  · exact h.1

lemma fan_le (A M : SimpleGraph V) : apex (oldPairs A M) (oldPairs A M) ≤ apex A M := by
  intro x y h
  cases x <;> cases y
  · exact h.elim
  · exact SimpleGraph.support_mono inf_le_left h
  · exact SimpleGraph.support_mono inf_le_left h
  · exact h.2

lemma apex_disjoint (A M : SimpleGraph V) (hm : IsMatching M) :
    Disjoint (apex (remaining A M) (newPairs A M)).edgeSet
      (apex (oldPairs A M) (oldPairs A M)).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e hcore hfan
  induction e using Sym2.ind with
  | h x y =>
    cases x <;> cases y
    · exact hcore.elim
    · exact Set.disjoint_left.mp (split_support_disjoint A M hm) hcore hfan
    · exact Set.disjoint_left.mp (split_support_disjoint A M hm) hcore hfan
    · exact hcore.2 hfan.1

lemma apex_cover (A M : SimpleGraph V) :
    (apex (remaining A M) (newPairs A M)).edgeSet ∪
      (apex (oldPairs A M) (oldPairs A M)).edgeSet = (apex A M).edgeSet := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    cases x <;> cases y
    · change False ∨ False ↔ False
      simp
    · exact Set.ext_iff.mp (support_split A M) _
    · exact Set.ext_iff.mp (support_split A M) _
    · change (_ ∧ ¬_) ∨ (_ ∧ _) ↔ _
      tauto

lemma even_left_of_disjoint_cover [Fintype V] {G A B : SimpleGraph V}
    (hd : Disjoint A.edgeSet B.edgeSet) (hu : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (heG : ∀ v, Even (G.degree v)) (heB : ∀ v, Even (B.degree v)) :
    ∀ v, Even (A.degree v) := by
  have heq : A ⊔ B = G := SimpleGraph.edgeSet_injective (by rw [edgeSet_sup,hu])
  intro v
  have hs := degree_sup_of_edge_disjoint A B hd v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,heq] at hs
  obtain ⟨r,hr⟩ := heG v
  obtain ⟨s,hs'⟩ := heB v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hr hs' ⊢
  exact ⟨r-s,by omega⟩

lemma even_toggled [Fintype V] (A M : SimpleGraph V) (hm : IsMatching M)
    (he : ∀ v, Even ((apex A M).degree v)) : ∀ v, Even ((toggled A M).degree v) := by
  have hO := IsMatching.mono hm (show oldPairs A M ≤ M from inf_le_left)
  have hcore := even_left_of_disjoint_cover (apex_disjoint A M hm) (apex_cover A M) he
    (by
      intro v
      have hv := fan_even (oldPairs A M) hO v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hv)
  have hdis : Disjoint (remaining A M).edgeSet (newPairs A M).edgeSet := by
    rw [edgeSet_sdiff,edgeSet_sdiff]
    exact Set.disjoint_sdiff_left.mono_right Set.diff_subset
  have hN := IsMatching.mono hm (show newPairs A M ≤ M from sdiff_le)
  have h := (even_apex_iff (remaining A M) (newPairs A M) hN hdis).mp (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hcore v)
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using h v

set_option maxHeartbeats 800000 in
/-- The mixed lifting estimate, where only genuinely new matching edges count
as marked. Existing-edge pairs are restored as triangle pieces. -/
lemma lift_decomposition [Fintype V] (A M : SimpleGraph V) (hm : IsMatching M)
    (D : Finset (toggled A M).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (toggled A M) D) :
    ∃ E : Finset (apex A M).Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (apex A M) E ∧
      E.card + (D.filter (fun H => (H.edgeSet ∩ (newPairs A M).edgeSet).Nonempty)).card ≤
        D.card + M.edgeSet.ncard := by
  have hN := IsMatching.mono hm (show newPairs A M ≤ M from sdiff_le)
  have hO := IsMatching.mono hm (show oldPairs A M ≤ M from inf_le_left)
  have hdis : Disjoint (remaining A M).edgeSet (newPairs A M).edgeSet := by
    rw [edgeSet_sdiff,edgeSet_sdiff]
    exact Set.disjoint_sdiff_left.mono_right Set.diff_subset
  obtain ⟨E,hcE,hdE,hbE⟩ := MatchingSmoothing.lift_decomposition
    (remaining A M) (newPairs A M) hN hdis D (by
      intro H hH
      refine ⟨(hc H hH).1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hc H hH).2 v) hd
  obtain ⟨F,hcF,hdF,hbF⟩ := fan_decomposition (oldPairs A M) hO
  obtain ⟨J,hcJ,hdJ,hbJ⟩ := combine_pure_decompositions (core_le A M) (fan_le A M)
    (apex_disjoint A M hm) (apex_cover A M) E F (by
      intro H hH
      refine ⟨(hcE H hH).1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcE H hH).2 v)
    (by
      intro H hH
      refine ⟨(hcF H hH).1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcF H hH).2 v)
    hdE hdF
  refine ⟨J,?_,hdJ,?_⟩
  · intro H hH
    refine ⟨(hcJ H hH).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcJ H hH).2 v
  · have hcard := pair_card_split A M
    have hbE' : E.card + (D.filter (fun H => (H.edgeSet ∩ (newPairs A M).edgeSet).Nonempty)).card ≤
        D.card + (newPairs A M).edgeSet.ncard := by
      convert hbE using 1
    omega

lemma bound_apex_of_small_matching [Fintype V] (C : ℕ)
    (A M : SimpleGraph V) (hm : IsMatching M) (hne : newPairs A M ≠ ⊥)
    (hr : M.edgeSet.ncard ≤ C+1)
    (D : Finset (toggled A M).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (toggled A M) D) (hb : D.card ≤ C * Fintype.card V) :
    ∃ E : Finset (apex A M).Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (apex A M) E ∧ E.card ≤ C * Fintype.card (Option V) := by
  obtain ⟨E,hcE,hdE,hbE⟩ := lift_decomposition A M hm D hc hd
  refine ⟨E,hcE,hdE,?_⟩
  have hq : 0 < (D.filter (fun H => (H.edgeSet ∩ (newPairs A M).edgeSet).Nonempty)).card := by
    convert MatchingSmoothing.marked_card_pos hne D hd using 1
  rw [Fintype.card_option,Nat.mul_add,Nat.mul_one]
  omega

end MixedSmoothing
end Erdos184
