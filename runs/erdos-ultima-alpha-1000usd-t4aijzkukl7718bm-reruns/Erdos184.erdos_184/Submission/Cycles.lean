import Submission.Work

/-! Auxiliary results on ordinary cycle decompositions of even-degree graphs.
These results do not establish the linear bound in Erdős 184. -/

open SimpleGraph
open scoped Classical
namespace Erdos184

lemma component_degree {V : Type*} [Fintype V] (G : SimpleGraph V)
    (C : G.ConnectedComponent) (v : C) : C.toSimpleGraph.degree v = G.degree v.val := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  apply Fintype.card_congr
  exact {
    toFun := fun w => ⟨w.val.val, w.property⟩
    invFun := fun w => ⟨⟨w.val, C.mem_supp_of_adj_mem_supp v.property w.property⟩, w.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma even_acyclic_eq_bot {V : Type*} [Fintype V] (G : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) (hacyc : G.IsAcyclic) : G = ⊥ := by
  ext u v
  simp only [bot_adj, iff_false]
  intro huv
  let C := G.connectedComponentMk u
  have hu : u ∈ C.supp := ConnectedComponent.connectedComponentMk_mem
  have hv : v ∈ C.supp := C.mem_supp_of_adj_mem_supp hu huv
  haveI : Nontrivial C := ⟨⟨⟨u, hu⟩, ⟨v, hv⟩, fun h => huv.ne (congrArg Subtype.val h)⟩⟩
  have ht : C.toSimpleGraph.IsTree :=
    ⟨C.connected_toSimpleGraph, hacyc.comap C.toSimpleGraph_hom Subtype.val_injective⟩
  obtain ⟨w, hw⟩ := ht.exists_vert_degree_one_of_nontrivial
  rw [component_degree] at hw
  have hh := heven w.val
  rw [hw] at hh
  exact (by decide : ¬Even (1 : ℕ)) hh

lemma exists_cycle_of_even_nonempty {V : Type*} [Fintype V] (G : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) (hne : G ≠ ⊥) :
    ∃ v, ∃ p : G.Walk v v, p.IsCycle := by
  by_contra! h
  exact hne (even_acyclic_eq_bot G heven h)

lemma cycle_subgraph_regular {V : Type*} [Fintype V] (G : SimpleGraph V)
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    p.toSubgraph.coe.Connected ∧ p.toSubgraph.coe.IsRegularOfDegree 2 := by
  refine ⟨p.toSubgraph_connected, ?_⟩
  intro w
  rw [Subgraph.coe_degree, Subgraph.degree, ← Nat.card_eq_fintype_card]
  exact hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp w.property)

lemma degree_sdiff_of_le {V : Type*} [Fintype V] {G H : SimpleGraph V}
    (h : H ≤ G) (v : V) : (G \ H).degree v = G.degree v - H.degree v := by
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq]
  change (G.neighborSet v \ H.neighborSet v).ncard = _
  exact Set.ncard_diff (fun _ hw => h hw)

lemma even_cycle_spanning {V : Type*} [Fintype V] {G : SimpleGraph V}
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    ∀ x, Even (p.toSubgraph.spanningCoe.degree x) := by
  intro x
  rw [Subgraph.degree_spanningCoe]
  by_cases hx : x ∈ p.toSubgraph.verts
  · have h2 : p.toSubgraph.degree x = 2 := by
      rw [Subgraph.degree, ← Nat.card_eq_fintype_card]
      exact hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp hx)
    rw [h2]
    decide
  · rw [Subgraph.degree_of_notMem_verts hx]
    decide

lemma even_delete_cycle {V : Type*} [Fintype V] {G : SimpleGraph V}
    (heven : ∀ x, Even (G.degree x)) {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    ∀ x, Even ((G \ p.toSubgraph.spanningCoe).degree x) := by
  intro x
  rw [degree_sdiff_of_le p.toSubgraph.spanningCoe_le]
  obtain ⟨a, ha⟩ := heven x
  obtain ⟨b, hb⟩ := even_cycle_spanning hp x
  refine ⟨a - b, ?_⟩
  omega

lemma even_cycle_decomposition {V : Type*} [Fintype V] (G : SimpleGraph V)
    (heven : ∀ x, Even (G.degree x)) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧ IsDecomposition G D := by
  classical
  generalize hn : G.edgeFinset.card = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hbot : G = ⊥
    · subst G
      exact ⟨∅, by simp, by simp [IsDecomposition]⟩
    obtain ⟨v, p, hp⟩ := exists_cycle_of_even_nonempty G heven hbot
    let H := p.toSubgraph
    let A := G \ H.spanningCoe
    have hA : A ≤ G := sdiff_le
    have heH : s(v, p.snd) ∈ H.spanningCoe.edgeFinset := by
      simpa [H] using p.toSubgraph_adj_snd hp.not_nil
    have heG : s(v, p.snd) ∈ G.edgeFinset := by
      exact SimpleGraph.mem_edgeFinset.mpr (H.spanningCoe_le (SimpleGraph.mem_edgeFinset.mp heH))
    have hlt : A.edgeFinset.card < G.edgeFinset.card := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro e he
        exact SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono hA (SimpleGraph.mem_edgeFinset.mp he))
      · intro heq
        have heA : s(v, p.snd) ∈ A.edgeFinset := heq.symm ▸ heG
        simp [A, SimpleGraph.edgeFinset_sdiff, heH] at heA
    obtain ⟨D, hcy, hd⟩ := ih A.edgeFinset.card (by omega) A (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using even_delete_cycle heven hp) (by simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card])
    let E := D.image (promote hA)
    refine ⟨insert H E, ?_, ?_⟩
    · intro K hK
      rcases Finset.mem_insert.mp hK with rfl | hK
      · exact cycle_subgraph_regular G hp
      · obtain ⟨K, hmemK, rfl⟩ := Finset.mem_image.mp (show K ∈ D.image (promote hA) from hK)
        refine ⟨(hcy K hmemK).1, ?_⟩
        intro w
        have hw := (hcy K hmemK).2 w
        simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
          using hw
    have hdis : Disjoint H.edgeSet A.edgeSet := by
      change Disjoint H.edgeSet (G \ H.spanningCoe).edgeSet
      rw [SimpleGraph.edgeSet_sdiff]
      exact Set.disjoint_sdiff_right
    refine ⟨?_, ?_⟩
    · intro K hK L hL hne
      rcases Finset.mem_insert.mp hK with rfl | hK <;>
        rcases Finset.mem_insert.mp hL with rfl | hL
      · exact (hne rfl).elim
      · obtain ⟨L, hmemL, rfl⟩ := Finset.mem_image.mp (show L ∈ D.image (promote hA) from hL)
        exact hdis.mono_right L.edgeSet_subset
      · obtain ⟨K, hmemK, rfl⟩ := Finset.mem_image.mp (show K ∈ D.image (promote hA) from hK)
        exact hdis.symm.mono_left K.edgeSet_subset
      · obtain ⟨K, hmemK, rfl⟩ := Finset.mem_image.mp (show K ∈ D.image (promote hA) from hK)
        obtain ⟨L, hmemL, rfl⟩ := Finset.mem_image.mp (show L ∈ D.image (promote hA) from hL)
        exact hd.1 hmemK hmemL (fun h => hne (congrArg (promote hA) h))
    · ext e
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨K, _, he⟩
        exact K.edgeSet_subset he
      · intro he
        by_cases heH : e ∈ H.edgeSet
        · exact ⟨H, Finset.mem_insert_self _ _, heH⟩
        · have heA : e ∈ A.edgeSet := by
            change e ∈ (G \ H.spanningCoe).edgeSet
            rw [SimpleGraph.edgeSet_sdiff]
            exact ⟨he, heH⟩
          rw [← hd.2] at heA
          simp only [Set.mem_iUnion] at heA
          obtain ⟨K, hK, heK⟩ := heA
          exact ⟨promote hA K, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨K, hK, rfl⟩), heK⟩

lemma decomposition_edge_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : Finset G.Subgraph) (hd : IsDecomposition G D) :
    ∑ H ∈ D, H.edgeSet.ncard = G.edgeFinset.card := by
  classical
  have hdis : Set.PairwiseDisjoint (D : Set G.Subgraph)
      (fun H => H.edgeSet.toFinset) := by
    intro H hH K hK hne
    apply Finset.disjoint_left.mpr
    intro e heH heK
    exact Set.disjoint_left.mp (hd.1 hH hK hne)
      (Set.mem_toFinset.mp heH) (Set.mem_toFinset.mp heK)
  have hunion : D.biUnion (fun H => H.edgeSet.toFinset) = G.edgeFinset := by
    ext e
    simp only [Finset.mem_biUnion, Set.mem_toFinset, SimpleGraph.mem_edgeFinset]
    simpa using (Set.ext_iff.mp hd.2 e)
  rw [← hunion, Finset.card_biUnion hdis]
  apply Finset.sum_congr rfl
  intro H _
  exact Set.ncard_eq_toFinset_card' _

lemma cycle_edgeSet_nonempty {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H : G.Subgraph) (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    H.edgeSet.Nonempty := by
  obtain ⟨v⟩ := hc.nonempty
  have hdeg : 0 < H.coe.degree v := by rw [hr v]; omega
  obtain ⟨w, hvw⟩ := (H.coe.degree_pos_iff_exists_adj v).mp hdeg
  exact ⟨s(v.val, w.val), hvw⟩

lemma cycle_decomposition_card_le_edges {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : Finset G.Subgraph)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) : D.card ≤ G.edgeFinset.card := by
  rw [← decomposition_edge_card G D hd]
  calc
    D.card = ∑ H ∈ D, 1 := by simp
    _ ≤ ∑ H ∈ D, H.edgeSet.ncard := by
      apply Finset.sum_le_sum
      intro H hH
      exact Nat.succ_le_iff.mpr ((Set.ncard_pos (Set.toFinite _)).mpr (cycle_edgeSet_nonempty H (hcy H hH).1 (hcy H hH).2))

lemma minimum_cycle_decomposition {V : Type*} [Fintype V] (G : SimpleGraph V)
    (heven : ∀ x, Even (G.degree x)) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧ IsDecomposition G D ∧
      ∀ E : Finset G.Subgraph,
        (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
        IsDecomposition G E → D.card ≤ E.card := by
  classical
  let P (n : ℕ) := ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧ IsDecomposition G D ∧ D.card = n
  have hex : ∃ n, P n := by
    obtain ⟨D, hcy, hd⟩ := even_cycle_decomposition G heven
    exact ⟨D.card, D, hcy, hd, rfl⟩
  obtain ⟨D, hcy, hd, hcard⟩ := Nat.find_spec hex
  refine ⟨D, hcy, hd, ?_⟩
  intro E hce hde
  rw [hcard]
  exact Nat.find_min' hex ⟨E, hce, hde, rfl⟩

lemma cycle_edgeSet_three_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H : G.Subgraph) (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    3 ≤ H.edgeSet.ncard := by
  classical
  obtain ⟨v⟩ := hc.nonempty
  have hv := H.coe.degree_lt_card_verts v
  have hr' : ∀ w, Nat.card (H.coe.neighborSet w) = 2 := by
    intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hr w
  have hs := H.coe.sum_degrees_eq_twice_card_edges
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hv hs
  rw [hr' v] at hv
  simp_rw [hr'] at hs
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card] at hs
  have hm := coe_edgeFinset_card G H
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hm hs
  rw [hm] at hs
  omega

lemma cycle_decomposition_three_mul_card_le_edges {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) : 3 * D.card ≤ G.edgeFinset.card := by
  rw [← decomposition_edge_card G D hd]
  calc
    3 * D.card = ∑ H ∈ D, 3 := by simp [mul_comm]
    _ ≤ ∑ H ∈ D, H.edgeSet.ncard := by
      apply Finset.sum_le_sum
      intro H hH
      exact cycle_edgeSet_three_le H (hcy H hH).1 (hcy H hH).2

lemma decomposition_degree_sum {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : Finset G.Subgraph) (hd : IsDecomposition G D) (v : V) :
    ∑ H ∈ D, H.degree v = G.degree v := by
  classical
  have hdis : Set.PairwiseDisjoint (D : Set G.Subgraph)
      (fun H => (H.neighborSet v).toFinset) := by
    intro H hH K hK hne
    apply Finset.disjoint_left.mpr
    intro w hwH hwK
    have ha : H.Adj v w := by simpa using hwH
    have hb : K.Adj v w := by simpa using hwK
    exact Set.disjoint_left.mp (hd.1 hH hK hne)
      (show s(v, w) ∈ H.edgeSet from ha)
      (show s(v, w) ∈ K.edgeSet from hb)
  have hunion : D.biUnion (fun H => (H.neighborSet v).toFinset) = G.neighborFinset v := by
    ext w
    simpa using (Set.ext_iff.mp hd.2 s(v, w))
  rw [SimpleGraph.degree, ← hunion, Finset.card_biUnion hdis]
  apply Finset.sum_congr rfl
  intro H _
  simp only [Subgraph.degree, Set.toFinset_card, ← Nat.card_eq_fintype_card]

lemma cycle_decomposition_vertex_count {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (v : V) :
    2 * (D.filter (fun H => v ∈ H.verts)).card = G.degree v := by
  classical
  rw [← decomposition_degree_sum G D hd v, Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H hH
  by_cases hv : v ∈ H.verts
  · simp only [hv, ↓reduceIte, mul_one]
    have hh := (hcy H hH).2 ⟨v, hv⟩
    rw [Subgraph.coe_degree] at hh
    simpa only [Subgraph.degree, ← Nat.card_eq_fintype_card] using hh.symm
  · simp [hv, Subgraph.degree_of_notMem_verts hv]

lemma replace_decomposition {V : Type*} (G : SimpleGraph V)
    (D S E : Finset G.Subgraph) (hd : IsDecomposition G D) (hs : S ⊆ D)
    (he : Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H => H.edgeSet))
    (hcover : (⋃ H ∈ E, H.edgeSet) = ⋃ H ∈ S, H.edgeSet) :
    IsDecomposition G ((D \ S) ∪ E) ∧
      ((D \ S) ∪ E).card ≤ D.card - S.card + E.card := by
  classical
  have hcross : ∀ H ∈ D \ S, ∀ K ∈ E, Disjoint H.edgeSet K.edgeSet := by
    intro H hH K hK
    apply Set.disjoint_left.mpr
    intro e heH heK
    have hem : e ∈ ⋃ L ∈ E, L.edgeSet := by
      simp only [Set.mem_iUnion]
      exact ⟨K, hK, heK⟩
    rw [hcover] at hem
    simp only [Set.mem_iUnion] at hem
    obtain ⟨L, hL, heL⟩ := hem
    have hne : H ≠ L := by
      intro h
      subst L
      exact (Finset.mem_sdiff.mp hH).2 hL
    exact Set.disjoint_left.mp (hd.1 (Finset.mem_sdiff.mp hH).1 (hs hL) hne) heH heL
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro H hH K hK hne
    rcases Finset.mem_union.mp hH with hH | hH <;>
      rcases Finset.mem_union.mp hK with hK | hK
    · exact hd.1 (Finset.mem_sdiff.mp hH).1 (Finset.mem_sdiff.mp hK).1 hne
    · exact hcross H hH K hK
    · exact (hcross K hK H hH).symm
    · exact he hH hK hne
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H, _, heH⟩
      exact H.edgeSet_subset heH
    · intro heG
      rw [← hd.2] at heG
      simp only [Set.mem_iUnion] at heG
      obtain ⟨H, hH, heH⟩ := heG
      by_cases hHS : H ∈ S
      · have hem : e ∈ ⋃ K ∈ S, K.edgeSet := by
          simp only [Set.mem_iUnion]
          exact ⟨H, hHS, heH⟩
        rw [← hcover] at hem
        simp only [Set.mem_iUnion] at hem
        obtain ⟨K, hK, heK⟩ := hem
        exact ⟨K, Finset.mem_union_right _ hK, heK⟩
      · exact ⟨H, Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hH, hHS⟩), heH⟩
  · exact (Finset.card_union_le _ _).trans_eq (by rw [Finset.card_sdiff_of_subset hs])

lemma minimum_cycle_subfamily {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : Finset G.Subgraph)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hmin : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (S E : Finset G.Subgraph) (hs : S ⊆ D)
    (hec : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (he : Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H => H.edgeSet))
    (hcover : (⋃ H ∈ E, H.edgeSet) = ⋃ H ∈ S, H.edgeSet) : S.card ≤ E.card := by
  classical
  obtain ⟨hd', hcard⟩ := replace_decomposition G D S E hd hs he hcover
  have hc' : ∀ H ∈ (D \ S) ∪ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · exact hcy H (Finset.mem_sdiff.mp hH).1
    · exact hec H hH
  have hm := hmin _ hc' hd'
  have hle := Finset.card_le_card hs
  omega

def unionPieces {V : Type*} (G : SimpleGraph V) (S : Finset G.Subgraph) : SimpleGraph V :=
  (S.sup id).spanningCoe

lemma unionPieces_le {V : Type*} (G : SimpleGraph V) (S : Finset G.Subgraph) :
    unionPieces G S ≤ G := (S.sup id).spanningCoe_le

lemma unionPieces_edgeSet {V : Type*} (G : SimpleGraph V) (S : Finset G.Subgraph) :
    (unionPieces G S).edgeSet = ⋃ H ∈ S, H.edgeSet := by
  change (S.sup id).edgeSet = _
  simp [Finset.sup_eq_iSup, Subgraph.edgeSet_iSup]

lemma unionPieces_neighborSet {V : Type*} (G : SimpleGraph V) (S : Finset G.Subgraph) (v : V) :
    (unionPieces G S).neighborSet v = ⋃ H ∈ S, H.neighborSet v := by
  change (S.sup id).neighborSet v = _
  simp [Finset.sup_eq_iSup, Subgraph.neighborSet_iSup]

lemma unionPieces_degree {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset G.Subgraph)
    (hs : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet)) (v : V) :
    (unionPieces G S).degree v = ∑ H ∈ S, H.degree v := by
  classical
  have hdis : Set.PairwiseDisjoint (S : Set G.Subgraph)
      (fun H => (H.neighborSet v).toFinset) := by
    intro H hH K hK hne
    apply Finset.disjoint_left.mpr
    intro w hwH hwK
    have ha : H.Adj v w := by simpa using hwH
    have hb : K.Adj v w := by simpa using hwK
    exact Set.disjoint_left.mp (hs hH hK hne)
      (show s(v, w) ∈ H.edgeSet from ha) (show s(v, w) ∈ K.edgeSet from hb)
  have hunion : S.biUnion (fun H => (H.neighborSet v).toFinset) =
      (unionPieces G S).neighborFinset v := by
    ext w
    simpa using (Set.ext_iff.mp (unionPieces_neighborSet G S v) w).symm
  rw [SimpleGraph.degree, ← hunion, Finset.card_biUnion hdis]
  apply Finset.sum_congr rfl
  intro H _
  simp only [Subgraph.degree, Set.toFinset_card, ← Nat.card_eq_fintype_card]

lemma unionPieces_edge_card {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset G.Subgraph)
    (hs : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet)) :
    (unionPieces G S).edgeFinset.card = ∑ H ∈ S, H.edgeSet.ncard := by
  classical
  have hdis : Set.PairwiseDisjoint (S : Set G.Subgraph)
      (fun H => H.edgeSet.toFinset) := by
    intro H hH K hK hne
    apply Finset.disjoint_left.mpr
    intro e heH heK
    exact Set.disjoint_left.mp (hs hH hK hne)
      (Set.mem_toFinset.mp heH) (Set.mem_toFinset.mp heK)
  have hunion : S.biUnion (fun H => H.edgeSet.toFinset) = (unionPieces G S).edgeFinset := by
    ext e
    simpa using (Set.ext_iff.mp (unionPieces_edgeSet G S) e).symm
  rw [← hunion, Finset.card_biUnion hdis]
  apply Finset.sum_congr rfl
  intro H _
  exact (Set.ncard_eq_toFinset_card' _).symm

lemma regular_two_piece_degree_even {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H : G.Subgraph) (hr : H.coe.IsRegularOfDegree 2) (v : V) : Even (H.degree v) := by
  by_cases hv : v ∈ H.verts
  · have hh := hr ⟨v, hv⟩
    rw [Subgraph.coe_degree] at hh
    have hh' : H.degree v = 2 := by
      simpa only [Subgraph.degree, ← Nat.card_eq_fintype_card] using hh
    rw [hh']
    decide
  · rw [Subgraph.degree_of_notMem_verts hv]
    decide

lemma refine_even_decomposition {V : Type*} [Fintype V] (G : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hd : IsDecomposition G D) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card ≤ D.card := by
  classical
  let C := D.filter (fun H => H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
  let S := D \ C
  have hCD : C ⊆ D := Finset.filter_subset _ _
  have hSD : S ⊆ D := Finset.sdiff_subset
  have hCp : Set.PairwiseDisjoint (C : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hd.1 (hCD hH) (hCD hK) hne
  have hSp : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hd.1 (hSD hH) (hSD hK) hne
  have hc : ∀ H ∈ C, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 :=
    fun _ hH => (Finset.mem_filter.mp hH).2
  have hsedge : ∀ H ∈ S, H.edgeSet.ncard = 1 := by
    intro H hH
    rcases hD H (hSD hH) with hcy | he
    · have hcy' : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
        refine ⟨hcy.1, ?_⟩
        intro v
        simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
          using hcy.2 v
      exact ((Finset.mem_sdiff.mp hH).2 (Finset.mem_filter.mpr ⟨hSD hH, hcy'⟩)).elim
    · have hh := coe_edgeFinset_card G H
      simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at he hh
      exact hh.symm.trans he
  let A := unionPieces G S
  have hA : A ≤ G := unionPieces_le G S
  have hevenA : ∀ v, Even (A.degree v) := by
    intro v
    have hdeg := unionPieces_degree G S hSp v
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdeg ⊢
    rw [hdeg]
    have hsum : ∑ H ∈ S, H.degree v + ∑ H ∈ C, H.degree v = G.degree v :=
      (Finset.sum_sdiff hCD).trans (decomposition_degree_sum G D hd v)
    have hcev : Even (∑ H ∈ C, H.degree v) :=
      Finset.even_sum _ (fun H hH => regular_two_piece_degree_even H (hc H hH).2 v)
    obtain ⟨a, ha⟩ := heven v
    obtain ⟨b, hb⟩ := hcev
    refine ⟨a - b, ?_⟩
    omega
  have hAc : A.edgeFinset.card = S.card := by
    calc
      A.edgeFinset.card = ∑ H ∈ S, H.edgeSet.ncard := by
        simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
          using unionPieces_edge_card G S hSp
      _ = ∑ H ∈ S, 1 := Finset.sum_congr rfl hsedge
      _ = S.card := by simp
  obtain ⟨E, hcyE, hdE⟩ := even_cycle_decomposition A hevenA
  have hcardE : E.card ≤ S.card := by
    have hh := cycle_decomposition_card_le_edges A E hcyE hdE
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hh hAc
    exact hh.trans_eq hAc
  let F := E.image (promote hA)
  have hcyF : ∀ H ∈ F, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp (show H ∈ E.image (promote hA) from hH)
    refine ⟨(hcyE K hK).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcyE K hK).2 v
  have hFp : Set.PairwiseDisjoint (F : Set G.Subgraph) (fun H => H.edgeSet) := by
    intro H hH K hK hne
    obtain ⟨H, hmemH, rfl⟩ := Finset.mem_image.mp (show H ∈ E.image (promote hA) from hH)
    obtain ⟨K, hmemK, rfl⟩ := Finset.mem_image.mp (show K ∈ E.image (promote hA) from hK)
    exact hdE.1 hmemH hmemK (fun h => hne (congrArg (promote hA) h))
  have hFcover : (⋃ H ∈ F, H.edgeSet) = ⋃ H ∈ S, H.edgeSet := by
    rw [← unionPieces_edgeSet G S]
    change (⋃ H ∈ F, H.edgeSet) = A.edgeSet
    ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H, hH, he⟩
      obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp (show H ∈ E.image (promote hA) from hH)
      exact K.edgeSet_subset he
    · intro he
      rw [← hdE.2] at he
      simp only [Set.mem_iUnion] at he
      obtain ⟨K, hK, heK⟩ := he
      exact ⟨promote hA K, Finset.mem_image.mpr ⟨K, hK, rfl⟩, heK⟩
  obtain ⟨hd', hcard⟩ := replace_decomposition G D S F hd hSD hFp hFcover
  refine ⟨(D \ S) ∪ F, ?_, hd', ?_⟩
  · intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · apply hc H
      by_contra hnot
      exact (Finset.mem_sdiff.mp hH).2
        (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hH).1, hnot⟩)
    · exact hcyF H hH
  · have hcardF : F.card ≤ S.card := Finset.card_image_le.trans hcardE
    have hcardS := Finset.card_le_card hSD
    omega

universe u

lemma conjecture_iff_even_cycle_bound :
    (∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C : ℝ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ x, Even (G.degree x)) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ C * Fintype.card V) := by
  rw [conjecture_iff_even_bound]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro V _ _ G heven
    obtain ⟨D, hcy, hd, hb⟩ := hC G heven
    obtain ⟨E, hce, hde, hcard⟩ := refine_even_decomposition G heven D hcy hd
    refine ⟨E, hce, hde, ?_⟩
    exact (show (E.card : ℝ) ≤ D.card by exact_mod_cast hcard).trans hb
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro V _ _ G heven
    obtain ⟨D, hcy, hd, hb⟩ := hC G heven
    refine ⟨D, ?_, hd, hb⟩
    intro H hH
    left
    refine ⟨(hcy H hH).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcy H hH).2 v

noncomputable def cycleWeight {V : Type*} [Fintype V] (G : SimpleGraph V) (H : G.Subgraph) : ℝ :=
  ∑ v : V, if v ∈ H.verts then (G.degree v : ℝ)⁻¹ else 0

lemma cycle_weight_total {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : Finset G.Subgraph)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    2 * ∑ H ∈ D, cycleWeight G H =
      ((Finset.univ.filter (fun v : V => G.degree v ≠ 0)).card : ℝ) := by
  classical
  simp only [cycleWeight]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro v _
  have hcount := cycle_decomposition_vertex_count G D hcy hd v
  have hsum : (∑ H ∈ D, if v ∈ H.verts then (G.degree v : ℝ)⁻¹ else 0) =
      ((D.filter (fun H => v ∈ H.verts)).card : ℝ) * (G.degree v : ℝ)⁻¹ := by
    simp [Finset.sum_ite]
  rw [hsum]
  have hc : 2 * ((D.filter (fun H => v ∈ H.verts)).card : ℝ) = G.degree v := by
    exact_mod_cast hcount
  rw [← mul_assoc, hc]
  by_cases hv : G.degree v = 0
  · simp [hv]
  · have hv' : (G.degree v : ℝ) ≠ 0 := by exact_mod_cast hv
    simp [hv, hv']

lemma cycle_card_bound_of_weight_lower {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : Finset G.Subgraph)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (ε : ℝ) (hε : ∀ H ∈ D, ε ≤ cycleWeight G H) :
    2 * ε * (D.card : ℝ) ≤ Fintype.card V := by
  have hsum : ε * (D.card : ℝ) ≤ ∑ H ∈ D, cycleWeight G H := by
    calc
      ε * (D.card : ℝ) = ∑ _H ∈ D, ε := by simp [mul_comm]
      _ ≤ ∑ H ∈ D, cycleWeight G H := Finset.sum_le_sum hε
  have hm := cycle_weight_total G D hcy hd
  have hc : ((Finset.univ.filter (fun v : V => G.degree v ≠ 0)).card : ℝ) ≤
      Fintype.card V := by
    exact_mod_cast (Finset.card_filter_le (s := (Finset.univ : Finset V))
      (p := fun v => G.degree v ≠ 0))
  nlinarith

end Erdos184
