import Submission.MixedCritical

/-! Singleton pieces in a minimum mixed partition form a forest. This gives a
conditional route to a linear bound if a uniform singleton proportion is proved.
No such proportion is asserted here. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.MixedCritical
open RankCritical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma number_lt_edges_of_cycle (G : SimpleGraph V) {u : V}
    (p : G.Walk u u) (hp : p.IsCycle) : number G < G.edgeSet.ncard := by
  let H := p.toSubgraph
  let B := H.spanningCoe
  let J : B.Subgraph := {
    verts := H.verts
    Adj := H.Adj
    adj_sub h := h
    edge_vert := H.edge_vert
    symm := H.symm }
  have hcJ : IsCycleOrEdge J.coe := by
    have hh := cycle_subgraph_regular G hp
    refine Or.inl ⟨hh.1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh.2 v
  have hdJ : IsDecomposition B {J} := by
    constructor
    · simp
    · simp only [Finset.mem_singleton,Set.iUnion_iUnion_eq_left]
      rfl
  have hB := number_le B {J} (by simpa using hcJ) hdJ
  have hG := number_le_restriction_add_edges H.spanningCoe_le
  have hsum := Set.ncard_diff_add_ncard_of_subset (edgeSet_mono H.spanningCoe_le)
  rw [← edgeSet_sdiff] at hsum
  have hsize := trail_spanning_edge_card p hp.isTrail
  have hlen := hp.three_le_length
  simp only [Finset.card_singleton] at hB
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hsize
  change number B ≤ 1 at hB
  change number G ≤ number B + (G \ B).edgeSet.ncard at hG
  change (G \ B).edgeSet.ncard + B.edgeSet.ncard = G.edgeSet.ncard at hsum
  change B.edgeSet.ncard = p.length at hsize
  omega

lemma acyclic_of_number_eq_edges (G : SimpleGraph V)
    (h : number G = G.edgeSet.ncard) : G.IsAcyclic := by
  intro u p hp
  have hn := number_lt_edges_of_cycle G p hp
  omega

lemma minimum_mixed_subfamily (G : SimpleGraph V) (D S E : Finset G.Subgraph)
    (hcD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hd : IsDecomposition G D)
    (hmin : D.card = number G) (hs : S ⊆ D)
    (hcE : ∀ H ∈ E, IsCycleOrEdge H.coe)
    (he : Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H => H.edgeSet))
    (hcover : (⋃ H ∈ E, H.edgeSet) = ⋃ H ∈ S, H.edgeSet) :
    S.card ≤ E.card := by
  obtain ⟨hd',hcard⟩ := replace_decomposition G D S E hd hs he hcover
  have hc' : ∀ H ∈ (D \ S) ∪ E, IsCycleOrEdge H.coe := by
    intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · exact hcD H (Finset.mem_sdiff.mp hH).1
    · exact hcE H hH
  have hm := number_le G _ hc' hd'
  have hle := Finset.card_le_card hs
  omega

lemma subfamily_card_le_number (G : SimpleGraph V) (D S : Finset G.Subgraph)
    (hcD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hd : IsDecomposition G D)
    (hmin : D.card = number G) (hs : S ⊆ D) :
    S.card ≤ number (unionPieces G S) := by
  obtain ⟨E,hcE,hdE,hcard⟩ := minimum_exists (unionPieces G S)
  let hAG := unionPieces_le G S
  let F := E.image (promote hAG)
  have hcF : ∀ H ∈ F, IsCycleOrEdge H.coe := by
    intro H hH
    obtain ⟨X,hX,rfl⟩ := Finset.mem_image.mp hH
    rcases hcE X hX with hcy | hedge
    · left
      refine ⟨hcy.1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hcy.2 v
    · right
      simpa only [edgeFinset_card,← Nat.card_eq_fintype_card] using hedge
  have hdF : Set.PairwiseDisjoint (F : Set G.Subgraph) (fun H => H.edgeSet) := by
    intro H hH K hK hne
    obtain ⟨X,hX,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨Y,hY,rfl⟩ := Finset.mem_image.mp hK
    exact hdE.1 hX hY (fun h => hne (congrArg (promote hAG) h))
  have heF : (⋃ H ∈ F, H.edgeSet) = ⋃ H ∈ S, H.edgeSet := by
    rw [← unionPieces_edgeSet G S,← hdE.2]
    ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H,hH,he⟩
      obtain ⟨X,hX,rfl⟩ := Finset.mem_image.mp hH
      exact ⟨X,hX,he⟩
    · rintro ⟨H,hH,he⟩
      exact ⟨promote hAG H,Finset.mem_image.mpr ⟨H,hH,rfl⟩,he⟩
  exact (minimum_mixed_subfamily G D S F hcD hd hmin hs hcF hdF heF).trans
    (Finset.card_image_le.trans_eq hcard)

lemma singleton_subfamily_forest (G : SimpleGraph V) (D S : Finset G.Subgraph)
    (hcD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hd : IsDecomposition G D)
    (hmin : D.card = number G) (hs : S ⊆ D)
    (hedge : ∀ H ∈ S, H.edgeSet.ncard = 1) :
    (unionPieces G S).IsAcyclic ∧ (unionPieces G S).edgeSet.ncard = S.card := by
  have hdS : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hd.1 (hs hH) (hs hK) hne
  have hcard := unionPieces_edge_card G S hdS
  rw [Finset.sum_congr rfl hedge] at hcard
  simp only [Finset.sum_const,smul_eq_mul,mul_one,edgeFinset_card,
    ← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hcard
  have hlow := subfamily_card_le_number G D S hcD hd hmin hs
  refine ⟨acyclic_of_number_eq_edges _ ?_,hcard⟩
  exact Nat.le_antisymm (number_le_edges _) (hcard ▸ hlow)

lemma singleton_subfamily_card_le_rank (G : SimpleGraph V) (D S : Finset G.Subgraph)
    (hcD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hd : IsDecomposition G D)
    (hmin : D.card = number G) (hs : S ⊆ D)
    (hedge : ∀ H ∈ S, H.edgeSet.ncard = 1) : S.card ≤ graphRank G := by
  obtain ⟨hf,hcard⟩ := singleton_subfamily_forest G D S hcD hd hmin hs hedge
  have hr := BlockRankPotential.forest_rank (unionPieces G S) hf
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hr
  rw [hcard] at hr
  exact hr ▸ rank_mono (unionPieces_le G S)

/-- This is conditional: a minimum partition with enough singleton pieces
would have a rank-linear bound. The existence of that partition is not proved. -/
lemma number_le_of_singleton_proportion (G : SimpleGraph V)
    (D S : Finset G.Subgraph) (C : ℕ)
    (hcD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hd : IsDecomposition G D)
    (hmin : D.card = number G) (hs : S ⊆ D)
    (hedge : ∀ H ∈ S, H.edgeSet.ncard = 1) (hprop : D.card ≤ C*S.card) :
    number G ≤ C * graphRank G := by
  rw [← hmin]
  exact hprop.trans (Nat.mul_le_mul_left C
    (singleton_subfamily_card_le_rank G D S hcD hd hmin hs hedge))

/-- A uniform singleton proportion is sufficient on critical restrictions
only. The proportion remains an explicit hypothesis. -/
lemma bound_of_critical_singleton_proportion (G : SimpleGraph V) (C : ℕ)
    (hprop : ∀ H : SimpleGraph V, H ≤ G → ∀ k : ℕ, 0 < k → IsCritical k H →
      ∃ D S : Finset H.Subgraph,
        (∀ J ∈ D, IsCycleOrEdge J.coe) ∧ IsDecomposition H D ∧ D.card = k ∧
        S ⊆ D ∧ (∀ J ∈ S, J.edgeSet.ncard = 1) ∧ D.card ≤ C*S.card) :
    number G ≤ C * graphRank G := by
  apply bound_of_critical_subgraphs G (C * graphRank G)
  intro H hHG k hH
  by_cases hz : k = 0
  · rw [hz]; exact Nat.zero_le _
  obtain ⟨D,S,hc,hd,hcard,hs,hedge,hbalance⟩ := hprop H hHG k (Nat.pos_of_ne_zero hz) hH
  have hb := number_le_of_singleton_proportion H D S C hc hd
    (hcard.trans hH.1.symm) hs hedge hbalance
  rw [hH.1] at hb
  exact hb.trans (Nat.mul_le_mul_left C (rank_mono hHG))

universe u
lemma conjecture_of_critical_singleton_proportion (C : ℕ)
    (hprop : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (k : ℕ),
      0 < k → IsCritical k G → ∃ D S : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧ D.card = k ∧
        S ⊆ D ∧ (∀ H ∈ S, H.edgeSet.ncard = 1) ∧ D.card ≤ C*S.card) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_bound.mpr
  refine ⟨(C : ℝ),?_⟩
  intro V _ _ G _
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists G
  have hb := bound_of_critical_singleton_proportion G C
    (fun H _ k hk hH => hprop H k hk hH)
  refine ⟨D,hc,hd,?_⟩
  rw [hcard]
  exact_mod_cast hb.trans (Nat.mul_le_mul_left C (rank_le_card G))

end Erdos184.MixedCritical
