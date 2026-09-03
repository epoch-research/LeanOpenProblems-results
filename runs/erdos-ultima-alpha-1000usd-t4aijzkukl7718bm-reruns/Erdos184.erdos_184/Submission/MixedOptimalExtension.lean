import Submission.MixedSingletonForest

/-! Exact completion and lexicographic singleton optimization for mixed
partitions. These lemmas do not prove a uniform singleton proportion. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.MixedCritical
open RankCritical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1500000

noncomputable def singles {G : SimpleGraph V} (D : Finset G.Subgraph) :=
  D.filter (fun H => H.edgeSet.ncard = 1)

lemma singles_card_le {G : SimpleGraph V} (D : Finset G.Subgraph) :
    (singles D).card ≤ D.card := Finset.card_filter_le _ _

lemma mixed_edge_nonempty {G : SimpleGraph V} (H : G.Subgraph)
    (hc : IsCycleOrEdge H.coe) : H.edgeSet.Nonempty := by
  rcases hc with hc | he
  · apply cycle_edgeSet_nonempty H hc.1
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hc.2 v
  · rw [coe_edgeFinset_card] at he
    exact (Set.ncard_pos (Set.toFinite _)).mp (by omega)

lemma complete_mixed_packing (G : SimpleGraph V) (P : Finset G.Subgraph)
    (hcP : ∀ H ∈ P, IsCycleOrEdge H.coe)
    (hdP : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (F : Finset (G \ unionPieces G P).Subgraph)
    (hcF : ∀ H ∈ F, IsCycleOrEdge H.coe)
    (hdF : IsDecomposition (G \ unionPieces G P) F) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧ P ⊆ D ∧
      D.card = P.card + F.card ∧
      (singles D).card = (singles P).card + (singles F).card := by
  let hAG : G \ unionPieces G P ≤ G := sdiff_le
  let Q := F.image (promote hAG)
  let D := P ∪ Q
  have hdis : ∀ H ∈ P, ∀ K ∈ F, Disjoint H.edgeSet K.edgeSet := by
    intro H hH K _
    apply Set.disjoint_left.mpr
    intro e heH heK
    have heA := K.edgeSet_subset heK
    rw [edgeSet_sdiff] at heA
    apply heA.2
    rw [unionPieces_edgeSet]
    exact Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hH,heH⟩⟩
  have hpq : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro H hHP hHQ
    obtain ⟨K,hK,hKH⟩ := Finset.mem_image.mp hHQ
    obtain ⟨e,he⟩ := mixed_edge_nonempty H (hcP H hHP)
    have heK : e ∈ K.edgeSet := by
      rw [← promote_edgeSet hAG K, hKH]
      exact he
    exact Set.disjoint_left.mp (hdis H hHP K hK) he heK
  have hsing : singles Q = (singles F).image (promote hAG) := by
    ext H
    simp only [singles, Q, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨K,hK,rfl⟩,hs⟩
      exact ⟨K,⟨hK,hs⟩,rfl⟩
    · rintro ⟨K,⟨hK,hs⟩,rfl⟩
      exact ⟨⟨K,hK,rfl⟩,hs⟩
  refine ⟨D,?_,⟨?_,?_⟩,Finset.subset_union_left,?_,?_⟩
  · intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · exact hcP H hH
    · obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hH
      exact hcF K hK
  · intro H hH K hK hne
    rcases Finset.mem_union.mp hH with hH | hH <;>
      rcases Finset.mem_union.mp hK with hK | hK
    · exact hdP hH hK hne
    · obtain ⟨X,hX,rfl⟩ := Finset.mem_image.mp hK
      exact hdis H hH X hX
    · obtain ⟨X,hX,rfl⟩ := Finset.mem_image.mp hH
      exact (hdis K hK X hX).symm
    · obtain ⟨X,hX,rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨Y,hY,rfl⟩ := Finset.mem_image.mp hK
      exact hdF.1 hX hY (fun h => hne (congrArg (promote hAG) h))
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H,_,he⟩; exact H.edgeSet_subset he
    · intro heG
      by_cases heU : e ∈ (unionPieces G P).edgeSet
      · rw [unionPieces_edgeSet] at heU
        obtain ⟨H,heH⟩ := Set.mem_iUnion.mp heU
        obtain ⟨hH,heH⟩ := Set.mem_iUnion.mp heH
        exact ⟨H,Finset.mem_union_left _ hH,heH⟩
      · have heA : e ∈ (G \ unionPieces G P).edgeSet := by
          rw [edgeSet_sdiff]; exact ⟨heG,heU⟩
        rw [← hdF.2] at heA
        obtain ⟨H,heH⟩ := Set.mem_iUnion.mp heA
        obtain ⟨hH,heH⟩ := Set.mem_iUnion.mp heH
        exact ⟨promote hAG H,Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨H,hH,rfl⟩),heH⟩
  · dsimp only [D,Q]
    rw [Finset.card_union_of_disjoint hpq,
      Finset.card_image_of_injective _ (InvariantPartitions.promote_injective hAG)]
  · change ((P ∪ Q).filter _).card = _
    rw [Finset.filter_union, Finset.card_union_of_disjoint
      (hpq.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    change (singles P).card + (singles Q).card = _
    rw [hsing,Finset.card_image_of_injective _ (InvariantPartitions.promote_injective hAG)]

lemma number_le_packing_residual (G : SimpleGraph V) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, IsCycleOrEdge H.coe)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet)) :
    number G ≤ P.card + number (G \ unionPieces G P) := by
  obtain ⟨F,hcF,hdF,hcardF⟩ := minimum_exists (G \ unionPieces G P)
  obtain ⟨D,hcD,hdD,_,hcardD,_⟩ := complete_mixed_packing G P hc hd F hcF hdF
  have h := number_le G D hcD hdD
  omega

lemma IsCritical.piece_residual_number {G : SimpleGraph V} {k : ℕ}
    (hG : IsCritical k G) (H : G.Subgraph) (hc : IsCycleOrEdge H.coe) :
    number (G \ H.spanningCoe) + 1 = k := by
  have hne : G \ H.spanningCoe ≠ G := by
    obtain ⟨e,he⟩ := mixed_edge_nonempty H hc
    intro h
    have hm : e ∈ (G \ H.spanningCoe).edgeSet := h.symm ▸ H.edgeSet_subset he
    rw [edgeSet_sdiff] at hm
    exact hm.2 he
  have hlo := hG.2 _ sdiff_le hne
  have hup := number_le_packing_residual G {H} (by simpa using hc) (by simp)
  rw [CountCritical.singleton_union,Finset.card_singleton,hG.1] at hup
  omega

lemma IsCritical.piece_optimal_extension {G : SimpleGraph V} {k : ℕ}
    (hG : IsCritical k G) (H : G.Subgraph) (hc : IsCycleOrEdge H.coe) :
    ∃ D : Finset G.Subgraph,
      (∀ J ∈ D, IsCycleOrEdge J.coe) ∧ IsDecomposition G D ∧ H ∈ D ∧ D.card = k := by
  obtain ⟨F,hcF,hdF,hcardF⟩ := minimum_exists (G \ unionPieces G {H})
  obtain ⟨D,hcD,hdD,hsub,hcardD,_⟩ :=
    complete_mixed_packing G {H} (by simpa using hc) (by simp) F hcF hdF
  have hn := hG.piece_residual_number H hc
  have hcardF' : F.card = number (G \ H.spanningCoe) := by
    simpa only [CountCritical.singleton_union] using hcardF
  refine ⟨D,hcD,hdD,hsub (by simp),?_⟩
  simp only [Finset.card_singleton] at hcardD
  omega

lemma singleton_maximum_exists (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧ D.card = number G ∧
      ∀ E : Finset G.Subgraph,
        (∀ H ∈ E, IsCycleOrEdge H.coe) → IsDecomposition G E →
        E.card = number G → (singles E).card ≤ (singles D).card := by
  let P (c : ℕ) := ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
    D.card = number G ∧ D.card - (singles D).card = c
  have hex : ∃ c, P c := by
    obtain ⟨D,hc,hd,hcard⟩ := minimum_exists G
    exact ⟨_,D,hc,hd,hcard,rfl⟩
  obtain ⟨D,hcD,hdD,hcardD,hbest⟩ := Nat.find_spec hex
  refine ⟨D,hcD,hdD,hcardD,?_⟩
  intro E hcE hdE hcardE
  have h := Nat.find_min' hex (show P (E.card-(singles E).card) from
    ⟨E,hcE,hdE,hcardE,rfl⟩)
  have hD := singles_card_le D
  have hE := singles_card_le E
  omega

noncomputable def maximumSingles (G : SimpleGraph V) : ℕ :=
  (singles (Classical.choose (singleton_maximum_exists G))).card

lemma maximumSingles_spec (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      D.card = number G ∧ (singles D).card = maximumSingles G := by
  obtain ⟨hc,hd,hcard,_⟩ := Classical.choose_spec (singleton_maximum_exists G)
  exact ⟨_,hc,hd,hcard,rfl⟩

lemma singles_le_maximum (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, IsCycleOrEdge H.coe) (hd : IsDecomposition G D)
    (hcard : D.card = number G) : (singles D).card ≤ maximumSingles G :=
  (Classical.choose_spec (singleton_maximum_exists G)).2.2.2 D hc hd hcard

lemma maximumSingles_le_rank (G : SimpleGraph V) :
    maximumSingles G ≤ graphRank G := by
  obtain ⟨D,hc,hd,hcard,hs⟩ := maximumSingles_spec G
  rw [← hs]
  exact singleton_subfamily_card_le_rank G D (singles D) hc hd hcard
    (Finset.filter_subset _ _) (fun H hH => (Finset.mem_filter.mp hH).2)

/-- The count equality is indispensable: a packing need not extend optimally. -/
lemma maximumSingles_packing_bound (G : SimpleGraph V) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, IsCycleOrEdge H.coe)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hcount : P.card + number (G \ unionPieces G P) = number G) :
    (singles P).card + maximumSingles (G \ unionPieces G P) ≤ maximumSingles G := by
  obtain ⟨F,hcF,hdF,hcardF,hsF⟩ := maximumSingles_spec (G \ unionPieces G P)
  obtain ⟨D,hcD,hdD,_,hcardD,hsD⟩ := complete_mixed_packing G P hc hd F hcF hdF
  have h := singles_le_maximum G D hcD hdD (by omega)
  omega

lemma IsCritical.maximumSingles_piece_bound {G : SimpleGraph V} {k : ℕ}
    (hG : IsCritical k G) (H : G.Subgraph) (hc : IsCycleOrEdge H.coe) :
    (singles ({H} : Finset G.Subgraph)).card + maximumSingles (G \ H.spanningCoe)
      ≤ maximumSingles G := by
  have hn := hG.piece_residual_number H hc
  have h := maximumSingles_packing_bound G {H} (by simpa using hc) (by simp) (by
    rw [Finset.card_singleton,CountCritical.singleton_union,hG.1]
    omega)
  simpa only [CountCritical.singleton_union] using h

lemma IsCritical.maximumSingles_edge_bound {G : SimpleGraph V} {k : ℕ}
    (hG : IsCritical k G) (H : G.Subgraph) (he : H.edgeSet.ncard = 1) :
    maximumSingles (G \ H.spanningCoe) + 1 ≤ maximumSingles G := by
  have hc : IsCycleOrEdge H.coe := Or.inr (by rwa [coe_edgeFinset_card])
  have hh := hG.maximumSingles_piece_bound H hc
  simp only [singles,Finset.filter_singleton,he,ite_true,Finset.card_singleton] at hh
  omega

lemma partition_edge_bound (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, IsCycleOrEdge H.coe) (hd : IsDecomposition G D) :
    G.edgeSet.ncard ≤ (D.card - (singles D).card) * Fintype.card V + (singles D).card := by
  have hsD : singles D ⊆ D := Finset.filter_subset _ _
  have hs : ∀ H ∈ singles D, H.edgeSet.ncard = 1 :=
    fun H hH => (Finset.mem_filter.mp hH).2
  have hu : unionPieces G D = G := by
    apply edgeSet_injective
    rw [unionPieces_edgeSet,hd.2]
  have he := unionPieces_edge_card G D hd.1
  rw [hu] at he
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at he
  have hsum := Finset.sum_sdiff (f := fun H : G.Subgraph => H.edgeSet.ncard) hsD
  have hsmall : (∑ H ∈ singles D, H.edgeSet.ncard) = (singles D).card := by
    rw [Finset.sum_congr rfl hs]; simp
  have hlarge : (∑ H ∈ D \ singles D, H.edgeSet.ncard) ≤
      (D.card-(singles D).card) * Fintype.card V := by
    calc
      _ ≤ ∑ _H ∈ D \ singles D, Fintype.card V := by
        apply Finset.sum_le_sum
        intro H hH
        have hHD := (Finset.mem_sdiff.mp hH).1
        rcases hc H hHD with hcy | hedge
        · have hr : H.coe.IsRegularOfDegree 2 := by
            intro v
            simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
              using hcy.2 v
          rw [regular_two_edge_vertex_card H hr]
          simpa using Set.ncard_le_ncard (Set.subset_univ H.verts)
        · have hm : H ∈ singles D := Finset.mem_filter.mpr ⟨hHD,by
            rwa [coe_edgeFinset_card] at hedge⟩
          exact ((Finset.mem_sdiff.mp hH).2 hm).elim
      _ = _ := by simp [Finset.card_sdiff_of_subset hsD]
  change (∑ H ∈ D \ singles D, H.edgeSet.ncard) +
    (∑ H ∈ singles D, H.edgeSet.ncard) = ∑ H ∈ D, H.edgeSet.ncard at hsum
  rw [hsmall,← he] at hsum
  omega

/-- Lexicographic optimality passes to subfamilies of a fixed optimum. It does
not pass to arbitrary exact-count critical restrictions. -/
lemma singleton_maximum_subfamily (G : SimpleGraph V) (D S E : Finset G.Subgraph)
    (hcD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hd : IsDecomposition G D)
    (hmin : D.card = number G) (hmax : (singles D).card = maximumSingles G)
    (hs : S ⊆ D) (hcE : ∀ H ∈ E, IsCycleOrEdge H.coe)
    (he : Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H => H.edgeSet))
    (hcover : (⋃ H ∈ E, H.edgeSet) = ⋃ H ∈ S, H.edgeSet)
    (hcard : E.card = S.card) : (singles E).card ≤ (singles S).card := by
  obtain ⟨hd',hb⟩ := replace_decomposition G D S E hd hs he hcover
  have hc' : ∀ H ∈ (D \ S) ∪ E, IsCycleOrEdge H.coe := by
    intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · exact hcD H (Finset.mem_sdiff.mp hH).1
    · exact hcE H hH
  have hn := number_le G _ hc' hd'
  have hSD := Finset.card_le_card hs
  have hmin' : ((D \ S) ∪ E).card = number G := by omega
  have hdiff := Finset.card_sdiff_of_subset hs
  have hi := Finset.card_union_add_card_inter (D \ S) E
  have hdis : Disjoint (D \ S) E := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    apply Finset.card_eq_zero.mp
    omega
  have hh := singles_le_maximum G _ hc' hd' hmin'
  have heq : singles ((D \ S) ∪ E) = singles (D \ S) ∪ singles E := by
    exact Finset.filter_union _ _ _
  have hdis' : Disjoint (singles (D \ S)) (singles E) :=
    hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [heq,Finset.card_union_of_disjoint hdis',← hmax] at hh
  have hss : singles S ⊆ singles D := by
    intro H hH
    exact Finset.mem_filter.mpr ⟨hs (Finset.mem_filter.mp hH).1,
      (Finset.mem_filter.mp hH).2⟩
  have hsd : singles (D \ S) = singles D \ singles S := by
    ext H
    simp only [singles,Finset.mem_filter,Finset.mem_sdiff]
    aesop
  have hsc := Finset.card_sdiff_add_card_eq_card hss
  rw [hsd] at hh
  omega

universe u
/-- A numerical formulation of the remaining sufficient hypothesis. This
lemma does NOT assert that any uniform C satisfies it. -/
lemma conjecture_of_maximumSingles_bound (C : ℕ)
    (hbound : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (k : ℕ),
      0 < k → IsCritical k G → k ≤ C * maximumSingles G) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_of_critical_singleton_proportion C
  intro V _ G k hk hcrit
  obtain ⟨D,hc,hd,hcard,hs⟩ := maximumSingles_spec G
  refine ⟨D,singles D,hc,hd,hcard.trans hcrit.1,Finset.filter_subset _ _,?_,?_⟩
  · intro H hH
    exact (Finset.mem_filter.mp hH).2
  · rw [hcard,hcrit.1,hs]
    exact hbound G k hk hcrit

end Erdos184.MixedCritical
