import Submission.GatewayPacking
import Submission.LongCyclePacking

/-! Mixing two edge-disjoint cycles that share at least two vertices.
This local operation does not yet yield a linear global decomposition bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184

lemma forest_edge_card_lt_vertex_card {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (ha : G.IsAcyclic) : G.edgeFinset.card < Fintype.card V := by
  obtain ⟨T, hGT, hmax⟩ := exists_maximal_isAcyclic_of_le_isAcyclic
    (show G ≤ (⊤ : SimpleGraph V) from le_top) ha
  have ht : T.IsTree :=
    (connected_top.maximal_le_isAcyclic_iff_isTree le_top).mp hmax
  have hcard := ht.card_edgeFinset
  have hle := Finset.card_le_card (SimpleGraph.edgeFinset_mono hGT)
  omega

/-- A cycle piece contained in another cycle piece has exactly its edge set. -/
lemma cycle_piece_edge_eq_of_subset {V : Type*} [Fintype V]
    {G K : SimpleGraph V} (H : G.Subgraph) (J : K.Subgraph)
    (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2)
    (jc : J.coe.Connected) (jr : J.coe.IsRegularOfDegree 2)
    (hsub : J.edgeSet ⊆ H.edgeSet) : J.edgeSet = H.edgeSet := by
  let A := J.spanningCoe.induce H.verts
  have hAH : A ≤ H.coe := by
    intro u v huv
    exact hsub (show s(u.val,v.val) ∈ J.edgeSet from huv)
  have he : ∀ v : H.verts, Even (A.degree v) := by
    intro v
    have hh : J.spanningCoe.neighborSet v.val ⊆ H.verts := by
      intro w hw
      exact H.edge_vert (H.symm (hsub (show s(v.val,w) ∈ J.edgeSet from hw)))
    have heq := SimpleGraph.degree_induce_of_neighborSet_subset hh
    have hj := regular_two_piece_degree_even J jr v.val
    rw [← Subgraph.degree_spanningCoe] at hj
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at heq hj ⊢
    change Even (Nat.card ((J.spanningCoe.induce H.verts).neighborSet v))
    rwa [heq]
  have hA := even_subgraph_of_connected_regular_two H.coe hc (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hr v) A hAH he
  obtain ⟨e, heJ⟩ := cycle_edgeSet_nonempty J jc jr
  rcases hA with hbot | hfull
  · induction e using Sym2.ind with
    | h u v =>
      have heH := hsub heJ
      have h : A.Adj ⟨u, H.edge_vert heH⟩ ⟨v, H.edge_vert (H.symm heH)⟩ := heJ
      simp [hbot] at h
  · apply Set.Subset.antisymm hsub
    intro e heH
    induction e using Sym2.ind with
    | h u v =>
      have h : H.coe.Adj ⟨u, H.edge_vert heH⟩ ⟨v, H.edge_vert (H.symm heH)⟩ := heH
      have hh := hfull.symm ▸ h
      exact hh

lemma proper_cycle_subgraph_acyclic {V : Type*} [Fintype V]
    {G : SimpleGraph V} (H : G.Subgraph)
    (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2)
    (A : SimpleGraph V) (hAH : A ≤ H.spanningCoe)
    (e : Sym2 V) (heH : e ∈ H.edgeSet) (heA : e ∉ A.edgeSet) : A.IsAcyclic := by
  intro v p hp
  have hj := cycle_subgraph_regular A hp
  have heq := cycle_piece_edge_eq_of_subset H p.toSubgraph hc hr hj.1 hj.2
    (fun _ he => SimpleGraph.edgeSet_mono hAH (p.toSubgraph.edgeSet_subset he))
  exact heA (p.toSubgraph.edgeSet_subset (heq.symm ▸ heH))

/-- If all edges lie in two colors, and each color alone is acyclic,
every cycle piece meets both colors. -/
lemma cycle_hits_two_forests {V : Type*} [Fintype V]
    {G A B : SimpleGraph V} (hcover : G.edgeSet ⊆ A.edgeSet ∪ B.edgeSet)
    (hA : A.IsAcyclic) (hB : B.IsAcyclic) (H : G.Subgraph)
    (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    (H.edgeSet ∩ A.edgeSet).Nonempty ∧ (H.edgeSet ∩ B.edgeSet).Nonempty := by
  have h₁ := cycle_has_edge_outside_forest B hB H hc hr
  have h₂ := cycle_has_edge_outside_forest A hA H hc hr
  constructor
  · obtain ⟨e, heH, heB⟩ := h₁
    exact ⟨e, heH, (hcover (H.edgeSet_subset heH)).resolve_right heB⟩
  · obtain ⟨e, heH, heA⟩ := h₂
    exact ⟨e, heH, (hcover (H.edgeSet_subset heH)).resolve_left heA⟩


/-- Two edge-disjoint cycles sharing two vertices have a mixed cycle. -/
lemma two_cycles_have_mixed_piece {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H K : G.Subgraph) (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2)
    (kc : K.coe.Connected) (kr : K.coe.IsRegularOfDegree 2)
    (hdis : Disjoint H.edgeSet K.edgeSet) (hover : 2 ≤ (H.verts ∩ K.verts).ncard) :
    ∃ Q : (H.spanningCoe ⊔ K.spanningCoe).Subgraph,
      Q.coe.Connected ∧ Q.coe.IsRegularOfDegree 2 ∧
      (Q.edgeSet ∩ H.edgeSet).Nonempty ∧ (Q.edgeSet ∩ K.edgeSet).Nonempty := by
  let U := H.spanningCoe ⊔ K.spanningCoe
  let S := H.verts ∪ K.verts
  obtain ⟨e, he⟩ := cycle_edgeSet_nonempty H hc hr
  obtain ⟨f, hf⟩ := cycle_edgeSet_nonempty K kc kr
  let A := U.deleteEdges {e,f}
  have hAU : A ≤ U := SimpleGraph.deleteEdges_le _
  have hsupp : A.support ⊆ S := by
    intro v ⟨w, hw⟩
    rcases hAU hw with hH | hK
    · exact Or.inl (H.edge_vert hH)
    · exact Or.inr (K.edge_vert hK)
  have hcardU : U.edgeSet.ncard = H.edgeSet.ncard + K.edgeSet.ncard := by
    change (H.spanningCoe ⊔ K.spanningCoe).edgeSet.ncard = _
    rw [SimpleGraph.edgeSet_sup]
    exact Set.ncard_union_eq hdis
  have hs : S.ncard + 2 ≤ U.edgeSet.ncard := by
    have hv := Set.ncard_union_add_ncard_inter H.verts K.verts
    rw [regular_two_edge_vertex_card H hr, regular_two_edge_vertex_card K kr] at hcardU
    change (H.verts ∪ K.verts).ncard + 2 ≤ _
    omega
  have hdel : U.edgeSet.ncard ≤ A.edgeSet.ncard + 2 := by
    have hh := Set.ncard_le_ncard_diff_add_ncard U.edgeSet ({e,f} : Set (Sym2 V))
    have hp : ({e,f} : Set (Sym2 V)).ncard ≤ 2 := by
      simpa using Set.ncard_insert_le e ({f} : Set (Sym2 V))
    have heq : A.edgeSet = U.edgeSet \ {e,f} := SimpleGraph.edgeSet_deleteEdges _
    rw [← heq] at hh
    omega
  have hnot : ¬A.IsAcyclic := by
    intro ha
    haveI : Nonempty S := by
      obtain ⟨v⟩ := hc.nonempty
      exact ⟨⟨v.val, Or.inl v.property⟩⟩
    have hh := forest_edge_card_lt_vertex_card (A.induce S) (ha.induce S)
    have heq := SimpleGraph.card_edgeFinset_induce_of_support_subset hsupp
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] at hh heq
    omega
  obtain ⟨v, p, hp⟩ : ∃ v, ∃ p : A.Walk v v, p.IsCycle := by
    simpa only [SimpleGraph.IsAcyclic, not_forall, not_not] using hnot
  have hpc := cycle_subgraph_regular A hp
  let R := H.spanningCoe.deleteEdges {e}
  let B := K.spanningCoe.deleteEdges {f}
  have hR : R.IsAcyclic := proper_cycle_subgraph_acyclic H hc hr R
    (SimpleGraph.deleteEdges_le _) e he (by
      change e ∉ (H.spanningCoe.deleteEdges {e}).edgeSet
      rw [SimpleGraph.edgeSet_deleteEdges]
      simp only [Set.mem_diff, Set.mem_singleton_iff, not_true_eq_false, and_false,
        not_false_eq_true])
  have hB : B.IsAcyclic := proper_cycle_subgraph_acyclic K kc kr B
    (SimpleGraph.deleteEdges_le _) f hf (by
      change f ∉ (K.spanningCoe.deleteEdges {f}).edgeSet
      rw [SimpleGraph.edgeSet_deleteEdges]
      simp only [Set.mem_diff, Set.mem_singleton_iff, not_true_eq_false, and_false,
        not_false_eq_true])
  have hcover : A.edgeSet ⊆ R.edgeSet ∪ B.edgeSet := by
    intro a ha
    change a ∈ (U.deleteEdges {e,f}).edgeSet at ha
    rw [SimpleGraph.edgeSet_deleteEdges] at ha
    have hh : a ∈ H.edgeSet ∪ K.edgeSet ∧ a ∉ ({e,f} : Set (Sym2 V)) := by
      simpa only [U, SimpleGraph.edgeSet_sup] using ha
    rcases hh.1 with hH | hK
    · left
      rw [show R.edgeSet = H.edgeSet \ {e} from SimpleGraph.edgeSet_deleteEdges _]
      exact ⟨hH, fun he' => hh.2 (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp he')))⟩
    · right
      rw [show B.edgeSet = K.edgeSet \ {f} from SimpleGraph.edgeSet_deleteEdges _]
      exact ⟨hK, fun hf' => hh.2 (Set.mem_insert_of_mem e hf')⟩
  obtain ⟨hmR, hmB⟩ := cycle_hits_two_forests hcover hR hB p.toSubgraph hpc.1 hpc.2
  refine ⟨promote hAU p.toSubgraph, hpc.1, ?_, ?_, ?_⟩
  · intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hpc.2 w
  · obtain ⟨a, ha, hR⟩ := hmR
    exact ⟨a, ha, SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le _) hR⟩
  · obtain ⟨a, ha, hB⟩ := hmB
    exact ⟨a, ha, SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le _) hB⟩


lemma complete_cycle_packing_extension {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    (F : Finset (G \ unionPieces G D).Subgraph)
    (hcF : ∀ H ∈ F, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdF : IsDecomposition (G \ unionPieces G D) F) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ D ⊆ E ∧ E.card ≤ D.card + F.card := by
  let hAG : G \ unionPieces G D ≤ G := sdiff_le
  let E := D ∪ F.image (promote hAG)
  have hdis : ∀ H ∈ D, ∀ K ∈ F, Disjoint H.edgeSet K.edgeSet := by
    intro H hH K _
    apply Set.disjoint_left.mpr
    intro e heH heK
    have heA := K.edgeSet_subset heK
    rw [SimpleGraph.edgeSet_sdiff] at heA
    apply heA.2
    rw [unionPieces_edgeSet]
    simp only [Set.mem_iUnion]
    exact ⟨H, hH, heH⟩
  refine ⟨E, ?_, ⟨?_, ?_⟩, Finset.subset_union_left, ?_⟩
  · intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · exact hc H hH
    · obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hH
      refine ⟨(hcF K hK).1, ?_⟩
      intro v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hcF K hK).2 v
  · intro H hH K hK hne
    rcases Finset.mem_union.mp hH with hH | hH <;>
      rcases Finset.mem_union.mp hK with hK | hK
    · exact hd hH hK hne
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hK
      exact hdis H hH X hX
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      exact (hdis K hK X hX).symm
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hK
      exact hdF.1 hX hY (fun h => hne (congrArg (promote hAG) h))
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H, _, he⟩
      exact H.edgeSet_subset he
    · intro heG
      by_cases heU : e ∈ (unionPieces G D).edgeSet
      · rw [unionPieces_edgeSet] at heU
        simp only [Set.mem_iUnion] at heU
        obtain ⟨H, hH, heH⟩ := heU
        exact ⟨H, Finset.mem_union_left _ hH, heH⟩
      · have heA : e ∈ (G \ unionPieces G D).edgeSet := by
          rw [SimpleGraph.edgeSet_sdiff]
          exact ⟨heG, heU⟩
        rw [← hdF.2] at heA
        simp only [Set.mem_iUnion] at heA
        obtain ⟨H, hH, heH⟩ := heA
        exact ⟨promote hAG H,
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨H, hH, rfl⟩), heH⟩
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)


lemma even_union_two_cycle_pieces {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H K : G.Subgraph) (hr : H.coe.IsRegularOfDegree 2) (kr : K.coe.IsRegularOfDegree 2)
    (hdis : Disjoint H.edgeSet K.edgeSet) :
    ∀ v, Even ((H.spanningCoe ⊔ K.spanningCoe).degree v) := by
  intro v
  have hn : Disjoint (H.neighborSet v) (K.neighborSet v) := by
    apply Set.disjoint_left.mpr
    intro w hH hK
    exact Set.disjoint_left.mp hdis (show s(v,w) ∈ H.edgeSet from hH) hK
  have hh := Set.ncard_union_eq hn
  have heH := regular_two_piece_degree_even H hr v
  have heK := regular_two_piece_degree_even K kr v
  simp only [Subgraph.degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at heH heK
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq]
  change Even ((H.neighborSet v ∪ K.neighborSet v).ncard)
  rw [hh]
  exact heH.add heK

/-- The union of two edge-disjoint cycles with two shared vertices admits
a decomposition in which every piece uses both original colors. -/
lemma two_cycles_mixed_decomposition {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H K : G.Subgraph) (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2)
    (kc : K.coe.Connected) (kr : K.coe.IsRegularOfDegree 2)
    (hdis : Disjoint H.edgeSet K.edgeSet) (hover : 2 ≤ (H.verts ∩ K.verts).ncard) :
    ∃ D : Finset (H.spanningCoe ⊔ K.spanningCoe).Subgraph,
      (∀ Q ∈ D, Q.coe.Connected ∧ Q.coe.IsRegularOfDegree 2 ∧
        (Q.edgeSet ∩ H.edgeSet).Nonempty ∧ (Q.edgeSet ∩ K.edgeSet).Nonempty) ∧
      IsDecomposition (H.spanningCoe ⊔ K.spanningCoe) D := by
  let U := H.spanningCoe ⊔ K.spanningCoe
  obtain ⟨Q, qc, qr, qH, qK⟩ := two_cycles_have_mixed_piece H K hc hr kc kr hdis hover
  have hcy : ∀ J ∈ ({Q} : Finset U.Subgraph), J.coe.Connected ∧ J.coe.IsRegularOfDegree 2 := by
    intro J hJ
    obtain rfl := Finset.mem_singleton.mp hJ
    exact ⟨qc, qr⟩
  have hpair : Set.PairwiseDisjoint (({Q} : Finset U.Subgraph) : Set U.Subgraph)
      (fun J => J.edgeSet) := by simp
  have he := even_union_two_cycle_pieces H K hr kr hdis
  have heR := even_residual_of_cycle_packing U (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using he v) {Q} (by
      intro J hJ
      refine ⟨(hcy J hJ).1, ?_⟩
      intro v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hcy J hJ).2 v) hpair
  obtain ⟨E, hcE, hdE⟩ := even_cycle_decomposition (U \ unionPieces U {Q}) (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using heR v)
  obtain ⟨D, hcD, hdD, hQD, _⟩ := complete_cycle_packing_extension U {Q} (by
    intro J hJ
    refine ⟨(hcy J hJ).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcy J hJ).2 v) hpair E (by
      intro J hJ
      refine ⟨(hcE J hJ).1, ?_⟩
      intro v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hcE J hJ).2 v) hdE
  have hQ : Q ∈ D := hQD (Finset.mem_singleton_self Q)
  have hmeet (J : U.Subgraph) (hJ : J ∈ D) :
      (J.edgeSet ∩ H.edgeSet).Nonempty ∧ (J.edgeSet ∩ K.edgeSet).Nonempty := by
    by_cases hne : Q = J
    · subst J
      exact ⟨qH, qK⟩
    have hnone : ∀ L : G.Subgraph, L.coe.Connected → L.coe.IsRegularOfDegree 2 →
        (Q.edgeSet ∩ L.edgeSet).Nonempty → ¬J.edgeSet ⊆ L.edgeSet := by
      intro L lc lr qL hsub
      have hJL := cycle_piece_edge_eq_of_subset L J lc lr (hcD J hJ).1 (hcD J hJ).2 hsub
      obtain ⟨e, heQ, heL⟩ := qL
      exact Set.disjoint_left.mp (hdD.1 hQ hJ hne) heQ (by change e ∈ J.edgeSet; rw [hJL]; exact heL)
    constructor
    · by_contra hn
      apply hnone K kc kr qK
      intro e heJ
      have heU : e ∈ H.edgeSet ∪ K.edgeSet := by
        simpa only [U, SimpleGraph.edgeSet_sup] using J.edgeSet_subset heJ
      rcases heU with heH | heK
      · exact (hn ⟨e, heJ, heH⟩).elim
      · exact heK
    · by_contra hn
      apply hnone H hc hr qH
      intro e heJ
      have heU : e ∈ H.edgeSet ∪ K.edgeSet := by
        simpa only [U, SimpleGraph.edgeSet_sup] using J.edgeSet_subset heJ
      rcases heU with heH | heK
      · exact heH
      · exact (hn ⟨e, heJ, heK⟩).elim
  refine ⟨D, ?_, hdD⟩
  intro J hJ
  refine ⟨(hcD J hJ).1, ?_, hmeet J hJ⟩
  intro v
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    using (hcD J hJ).2 v


/-- Cycle pieces in a graph of vertex-disjoint cycles coincide whenever
they share a vertex. -/
lemma cycle_pieces_eq_in_isCycles {V : Type*} [Fintype V]
    {G₁ G₂ B : SimpleGraph V} (hb : B.IsCycles)
    (H : G₁.Subgraph) (K : G₂.Subgraph)
    (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2)
    (kc : K.coe.Connected) (kr : K.coe.IsRegularOfDegree 2)
    (hHB : H.edgeSet ⊆ B.edgeSet) (hKB : K.edgeSet ⊆ B.edgeSet)
    (hover : (H.verts ∩ K.verts).Nonempty) : H.edgeSet = K.edgeSet := by
  have hsat : ∀ v ∈ H.verts, H.neighborSet v = B.neighborSet v := by
    intro v hv
    have hh := hr ⟨v,hv⟩
    rw [Subgraph.coe_degree] at hh
    simp only [Subgraph.degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hh
    have hsub : H.neighborSet v ⊆ B.neighborSet v := by
      intro w hw
      exact hHB (show s(v,w) ∈ H.edgeSet from hw)
    have hne : (B.neighborSet v).Nonempty :=
      Set.Nonempty.mono hsub (Set.nonempty_of_ncard_ne_zero (by omega))
    apply Set.eq_of_subset_of_ncard_le hsub
    rw [hb hne, hh]
  have hprop : ∀ {x y : K.verts} (p : K.coe.Walk x y),
      x.val ∈ H.verts → y.val ∈ H.verts := by
    intro x y p
    induction p with
    | nil => exact id
    | @cons x y z hxy p ih =>
      intro hx
      have hH : H.Adj x.val y.val := by
        change y.val ∈ H.neighborSet x.val
        rw [hsat x.val hx]
        exact hKB (show s(x.val,y.val) ∈ K.edgeSet from hxy)
      exact ih (H.edge_vert (H.symm hH))
  obtain ⟨v, hvH, hvK⟩ := hover
  have hverts : ∀ w ∈ K.verts, w ∈ H.verts := by
    intro w hw
    obtain ⟨p⟩ := kc ⟨v,hvK⟩ ⟨w,hw⟩
    exact hprop p hvH
  have hsub : K.edgeSet ⊆ H.edgeSet := by
    intro e heK
    induction e using Sym2.ind with
    | h x y =>
      have hx := hverts x (K.edge_vert heK)
      change y ∈ H.neighborSet x
      rw [hsat x hx]
      exact hKB heK
  exact (cycle_piece_edge_eq_of_subset H K hc hr kc kr hsub).symm

/-- A valid local absorption step for a graph whose unmarked (blue) edges
form vertex-disjoint cycles. The two-vertex overlap is an essential input. -/
lemma absorb_blue_cycle {V : Type*} [Fintype V] {G R B : SimpleGraph V}
    (hblue : B.IsCycles) (H K : G.Subgraph)
    (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2)
    (kc : K.coe.Connected) (kr : K.coe.IsRegularOfDegree 2)
    (hdis : Disjoint H.edgeSet K.edgeSet) (hover : 2 ≤ (H.verts ∩ K.verts).ncard)
    (hKB : K.edgeSet ⊆ B.edgeSet)
    (hcover : H.edgeSet ∪ K.edgeSet ⊆ R.edgeSet ∪ B.edgeSet) :
    ∃ D : Finset (H.spanningCoe ⊔ K.spanningCoe).Subgraph,
      (∀ Q ∈ D, Q.coe.Connected ∧ Q.coe.IsRegularOfDegree 2 ∧
        (Q.edgeSet ∩ R.edgeSet).Nonempty) ∧
      IsDecomposition (H.spanningCoe ⊔ K.spanningCoe) D := by
  obtain ⟨D, hcD, hdD⟩ := two_cycles_mixed_decomposition H K hc hr kc kr hdis hover
  refine ⟨D, ?_, hdD⟩
  intro Q hQ
  refine ⟨(hcD Q hQ).1, ?_, ?_⟩
  · intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcD Q hQ).2.1 v
  by_contra hn
  have hQB : Q.edgeSet ⊆ B.edgeSet := by
    intro e heQ
    have heU : e ∈ H.edgeSet ∪ K.edgeSet := by
      simpa only [SimpleGraph.edgeSet_sup] using Q.edgeSet_subset heQ
    rcases hcover heU with heR | heB
    · exact (hn ⟨e,heQ,heR⟩).elim
    · exact heB
  have hv : (Q.verts ∩ K.verts).Nonempty := by
    obtain ⟨e, heQ, heK⟩ := (hcD Q hQ).2.2.2
    induction e using Sym2.ind with
    | h x y => exact ⟨x, Q.edge_vert heQ, K.edge_vert heK⟩
  have heq := cycle_pieces_eq_in_isCycles hblue Q K (hcD Q hQ).1
    (by
      intro v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hcD Q hQ).2.1 v) kc kr hQB hKB hv
  obtain ⟨e, heQ, heH⟩ := (hcD Q hQ).2.2.1
  rw [heq] at heQ
  exact Set.disjoint_left.mp hdis heH heQ

end Erdos184
