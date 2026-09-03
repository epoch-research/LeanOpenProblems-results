import Submission.Circumference

/-! Bounds on shortest-length pieces of a minimum cycle decomposition.
These do not provide a bound on the number of longer pieces. -/
open SimpleGraph
open scoped Classical
namespace Erdos184

lemma cycle_piece_card_ge_of_cycle_length_lower {V : Type*} [Fintype V]
    (G : SimpleGraph V) (g : ℕ)
    (hg : ∀ u (p : G.Walk u u), p.IsCycle → g ≤ p.length)
    (H : G.Subgraph) (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    g ≤ H.edgeSet.ncard := by
  obtain ⟨v⟩ := hc.nonempty
  have he : ∀ x, Even (H.coe.degree x) := by intro x; rw [hr x]; decide
  have hn : H.coe ≠ ⊥ := by
    intro hn
    have hv := hr v
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hv
    simp [hn] at hv
  obtain ⟨u, p, hp⟩ := exists_cycle_of_even_nonempty H.coe (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using he) hn
  have hlow := hg u.val (p.map H.hom) (hp.map Subtype.val_injective)
  simp only [Walk.length_map] at hlow
  have hupp := hp.isTrail.length_le_card_edgeFinset
  have hc := coe_edgeFinset_card G H
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hupp hc
  omega

lemma cycle_decomposition_girth_mul_card_le_edges {V : Type*} [Fintype V]
    (G : SimpleGraph V) (g : ℕ)
    (hg : ∀ u (p : G.Walk u u), p.IsCycle → g ≤ p.length)
    (D : Finset G.Subgraph)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) : g * D.card ≤ G.edgeFinset.card := by
  rw [← decomposition_edge_card G D hd]
  calc
    g * D.card = ∑ H ∈ D, g := by simp [mul_comm]
    _ ≤ ∑ H ∈ D, H.edgeSet.ncard := by
      apply Finset.sum_le_sum
      intro H hH
      exact cycle_piece_card_ge_of_cycle_length_lower G g hg H (hcy H hH).1 (hcy H hH).2

lemma cycle_refinement_girth_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (g : ℕ)
    (hg : ∀ u (p : G.Walk u u), p.IsCycle → g ≤ p.length)
    (he : ∀ v, Even (G.degree v)) {u : V} (p : G.Walk u u) (hp : p.IsCycle) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ g * E.card + p.length ≤ G.edgeFinset.card + g := by
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
  have hgA : ∀ u (q : A.Walk u u), q.IsCycle → g ≤ q.length := by
    intro u q hq
    have hh := hg u (q.mapLe hAG) (hq.mapLe hAG)
    simpa only [Walk.mapLe, Walk.length_map] using hh
  have hcardA := cycle_decomposition_girth_mul_card_le_edges A g hgA DA hcA hdA
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
  nlinarith [Nat.mul_le_mul_left g (hbE.trans hb0)]

lemma minimum_subfamily_girth_cycle_length_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (S : Finset G.Subgraph) (hs : S ⊆ D) (g : ℕ)
    (hg : ∀ u (q : (unionPieces G S).Walk u u), q.IsCycle → g ≤ q.length) {u : V}
    (p : (unionPieces G S).Walk u u) (hp : p.IsCycle) :
    g * S.card + p.length ≤ (∑ H ∈ S, H.edgeSet.ncard) + g := by
  have hdis : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hHK => hd.1 (hs hH) (hs hK) hHK
  have he : ∀ v, Even ((unionPieces G S).degree v) := by
    intro v
    have hdeg := unionPieces_degree G S hdis v
    have hev : Even (∑ H ∈ S, H.degree v) :=
      Finset.even_sum _ (fun H hH => regular_two_piece_degree_even H (hc H (hs hH)).2 v)
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdeg ⊢
    rwa [hdeg]
  obtain ⟨E, hcE, hdE, hcard⟩ := cycle_refinement_girth_bound (unionPieces G S) g hg he p hp
  have hmin := subfamily_minimum_for_union G D hc hd hm S hs E hcE hdE
  have hsum := unionPieces_edge_card G S hdis
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hcard hsum
  nlinarith [Nat.mul_le_mul_left g hmin]

lemma minimum_girth_subfamily_cycles {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (S : Finset G.Subgraph) (hs : S ⊆ D) (g : ℕ)
    (hg : ∀ u (q : (unionPieces G S).Walk u u), q.IsCycle → g ≤ q.length)
    (hlen : ∀ H ∈ S, H.edgeSet.ncard = g) {u : V}
    (p : (unionPieces G S).Walk u u) (hp : p.IsCycle) : p.length = g := by
  have hb := minimum_subfamily_girth_cycle_length_bound G D hc hd hm S hs g hg p hp
  have heq : (∑ H ∈ S, H.edgeSet.ncard) = g * S.card := by
    simp only [Finset.sum_congr rfl hlen, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [heq] at hb
  have hlow := hg u p hp
  omega

/-- A linear bound on equal-length pieces whose union has no shorter cycle.
In particular this applies to the girth-length pieces of a minimum decomposition. -/
lemma minimum_girth_subfamily_card_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (S : Finset G.Subgraph) (hs : S ⊆ D) (g : ℕ) (hg2 : 2 ≤ g)
    (hg : ∀ u (q : (unionPieces G S).Walk u u), q.IsCycle → g ≤ q.length)
    (hlen : ∀ H ∈ S, H.edgeSet.ncard = g) :
    g * S.card ≤ (g - 1) * Fintype.card V := by
  have hbound := edge_card_le_of_cycle_length_bound (unionPieces G S) g hg2
    (fun _ p hp => (minimum_girth_subfamily_cycles G D hc hd hm S hs g hg hlen p hp).le)
  have hdis : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hHK => hd.1 (hs hH) (hs hK) hHK
  have hsum := unionPieces_edge_card G S hdis
  have heq : (∑ H ∈ S, H.edgeSet.ncard) = g * S.card := by
    simp only [Finset.sum_congr rfl hlen, Finset.sum_const, smul_eq_mul, mul_comm]
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hsum hbound ⊢
  rw [hsum, heq] at hbound
  exact hbound

/-- In any minimum cycle decomposition, there are at most `|V|` pieces
whose length equals the girth of the ambient graph. -/
lemma minimum_girth_pieces_le_vertices {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card) :
    (D.filter (fun H => H.edgeSet.ncard = G.girth)).card ≤ Fintype.card V := by
  let S := D.filter (fun H => H.edgeSet.ncard = G.girth)
  have hs : S ⊆ D := Finset.filter_subset _ _
  have hlen : ∀ H ∈ S, H.edgeSet.ncard = G.girth :=
    fun _ hH => (Finset.mem_filter.mp hH).2
  by_cases ha : G.IsAcyclic
  · have hS : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro H hH
      have hh := cycle_edgeSet_three_le H (hc H (hs hH)).1 (hc H (hs hH)).2
      rw [hlen H hH, ha.girth_eq_zero] at hh
      omega
    change S.card ≤ _
    simp [hS]
  · have hg2 : 2 ≤ G.girth := (by omega : 2 ≤ 3).trans (G.three_le_girth ha)
    have hg : ∀ u (p : (unionPieces G S).Walk u u), p.IsCycle → G.girth ≤ p.length := by
      intro u p hp
      have hh := G.girth_le_length (hp.mapLe (unionPieces_le G S))
      simpa only [Walk.mapLe, Walk.length_map] using hh
    have hb := minimum_girth_subfamily_card_bound G D hc hd hm S hs G.girth hg2 hg hlen
    have hb' : G.girth * S.card ≤ G.girth * Fintype.card V :=
      hb.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
    exact Nat.le_of_mul_le_mul_left hb' (by omega)

end Erdos184
