import Submission.Cycles

/-! Structural bounds on short pieces of a minimum cycle decomposition.
These results do not prove a uniform linear bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184

lemma trail_spanning_edge_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hp : p.IsTrail) :
    p.toSubgraph.spanningCoe.edgeFinset.card = p.length := by
  have heq : p.toSubgraph.spanningCoe.edgeFinset = hp.edgesFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, Walk.IsTrail.edgesFinset, Finset.mem_mk,
      Multiset.mem_coe]
    exact p.mem_edges_toSubgraph
  rw [heq]
  simp only [Walk.IsTrail.edgesFinset, Finset.card_mk, Multiset.coe_card, Walk.length_edges]

/-- Removing any prescribed cycle gives an upper bound on the minimum number
of cycles in terms of the remaining number of edges. -/
lemma cycle_refinement_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) {u : V} (p : G.Walk u u) (hp : p.IsCycle) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ 3 * E.card + p.length ≤ G.edgeFinset.card + 3 := by
  let H := p.toSubgraph
  let A := G \ H.spanningCoe
  let B := H.spanningCoe
  have hAG : A ≤ G := sdiff_le
  have hBG : B ≤ G := H.spanningCoe_le
  have heA : ∀ v, Even (A.degree v) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using even_delete_cycle he hp
  obtain ⟨DA, hcA, hdA⟩ := even_cycle_decomposition A (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heA)
  have hcardA := cycle_decomposition_three_mul_card_le_edges A DA hcA hdA
  let J : B.Subgraph := {
    verts := H.verts
    Adj := H.Adj
    adj_sub h := h
    edge_vert := H.edge_vert
    symm := H.symm }
  have hcJ : IsCycleOrEdge J.coe := by
    have hh := cycle_subgraph_regular G hp
    refine Or.inl ⟨hh.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v
  have hdJ : IsDecomposition B {J} := by
    refine ⟨?_, ?_⟩
    · intro K hK L hL hKL
      simp only [Finset.mem_coe, Finset.mem_singleton] at hK hL
      exact (hKL (hK.trans hL.symm)).elim
    · simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
      rfl
  have hdis : Disjoint A.edgeSet B.edgeSet := by
    change Disjoint (G \ B).edgeSet B.edgeSet
    rw [SimpleGraph.edgeSet_sdiff]
    exact Set.disjoint_sdiff_left
  have hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet := by
    change (G \ B).edgeSet ∪ B.edgeSet = G.edgeSet
    rw [SimpleGraph.edgeSet_sdiff]
    exact Set.diff_union_of_subset (SimpleGraph.edgeSet_mono hBG)
  obtain ⟨E0, hc0, hd0, hb0⟩ := combine_decompositions hAG hBG hdis hcover DA {J}
    (by
      intro H hH
      refine Or.inl ⟨(hcA H hH).1, ?_⟩
      intro v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hcA H hH).2 v) (by simpa using hcJ) hdA hdJ
  obtain ⟨E, hcE, hdE, hbE⟩ := refine_even_decomposition G he E0 hc0 hd0
  refine ⟨E, hcE, hdE, ?_⟩
  have hsub : B.edgeFinset ⊆ G.edgeFinset := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr
      (SimpleGraph.edgeSet_mono hBG (SimpleGraph.mem_edgeFinset.mp he))
  have hcardB := trail_spanning_edge_card p hp.isTrail
  have hdiff : A.edgeFinset.card + B.edgeFinset.card = G.edgeFinset.card := by
    change (G \ B).edgeFinset.card + B.edgeFinset.card = _
    rw [SimpleGraph.edgeFinset_sdiff, Finset.card_sdiff_add_card_eq_card hsub]
  simp only [Finset.card_singleton] at hb0
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hcardA hcardB hdiff ⊢
  change Nat.card B.edgeSet = p.length at hcardB
  omega

lemma subfamily_minimum_for_union {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (S : Finset G.Subgraph) (hs : S ⊆ D)
    (E : Finset (unionPieces G S).Subgraph)
    (hcE : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdE : IsDecomposition (unionPieces G S) E) : S.card ≤ E.card := by
  let hAG := unionPieces_le G S
  let F := E.image (promote hAG)
  have hcF : ∀ H ∈ F, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
    refine ⟨(hcE X hX).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcE X hX).2 v
  have hdF : Set.PairwiseDisjoint (F : Set G.Subgraph) (fun H => H.edgeSet) := by
    intro H hH K hK hHK
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hK
    exact hdE.1 hX hY (fun h => hHK (congrArg (promote hAG) h))
  have heF : (⋃ H ∈ F, H.edgeSet) = ⋃ H ∈ S, H.edgeSet := by
    rw [← unionPieces_edgeSet G S, ← hdE.2]
    ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H, hH, he⟩
      obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      exact ⟨X, hX, he⟩
    · rintro ⟨H, hH, he⟩
      exact ⟨promote hAG H, Finset.mem_image.mpr ⟨H, hH, rfl⟩, he⟩
  exact (minimum_cycle_subfamily G D hc hd hm S F hs hcF hdF heF).trans Finset.card_image_le

lemma minimum_subfamily_cycle_length_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (S : Finset G.Subgraph) (hs : S ⊆ D) {u : V}
    (p : (unionPieces G S).Walk u u) (hp : p.IsCycle) :
    3 * S.card + p.length ≤ (∑ H ∈ S, H.edgeSet.ncard) + 3 := by
  have hdis : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hHK => hd.1 (hs hH) (hs hK) hHK
  have he : ∀ v, Even ((unionPieces G S).degree v) := by
    intro v
    have hdeg := unionPieces_degree G S hdis v
    have hev : Even (∑ H ∈ S, H.degree v) :=
      Finset.even_sum _ (fun H hH => regular_two_piece_degree_even H (hc H (hs hH)).2 v)
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdeg ⊢
    rwa [hdeg]
  obtain ⟨E, hcE, hdE, hcard⟩ := cycle_refinement_bound (unionPieces G S) he p hp
  have hmin := subfamily_minimum_for_union G D hc hd hm S hs E hcE hdE
  have hsum := unionPieces_edge_card G S hdis
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hcard hsum
  omega

/-- The triangle pieces of a minimum decomposition cannot have a longer cycle
in their edge union. -/
lemma minimum_triangle_subfamily_cycles {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (S : Finset G.Subgraph) (hs : S ⊆ D)
    (htri : ∀ H ∈ S, H.edgeSet.ncard = 3) {u : V}
    (p : (unionPieces G S).Walk u u) (hp : p.IsCycle) : p.length = 3 := by
  have hb := minimum_subfamily_cycle_length_bound G D hc hd hm S hs p hp
  have heq : (∑ H ∈ S, H.edgeSet.ncard) = 3 * S.card := by
    simp only [Finset.sum_congr rfl htri, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [heq] at hb
  have hlow := hp.three_le_length
  omega

end Erdos184
