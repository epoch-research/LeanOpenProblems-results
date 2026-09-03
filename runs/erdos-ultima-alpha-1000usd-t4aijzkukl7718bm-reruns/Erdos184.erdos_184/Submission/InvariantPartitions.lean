import Submission.MinimalCounterexample

/-!
Consequences of invariant cycle-partition size. This is a stronger hypothesis
than `AllCyclesOptimal`; the implication from optimal extendability to invariance
is not proved here. None of these results settles Erdos 184.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace InvariantPartitions

/-- All pure-cycle decompositions have the same number of pieces. -/
def HasInvariantCount {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ D E : Finset G.Subgraph,
    (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
    IsDecomposition G D →
    (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
    IsDecomposition G E → D.card = E.card

lemma promote_injective {V : Type*} {G A : SimpleGraph V} (hA : A ≤ G) :
    Function.Injective (promote hA) := by
  intro H K h
  exact Subgraph.ext (congrArg (fun L => L.verts) h) (congrArg (fun L => L.Adj) h)

/-- Invariance of full partitions passes to packings with the same edge union.
The evenness assumption is used to complete each packing. -/
lemma HasInvariantCount.packing_card_eq {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hi : HasInvariantCount G) (he : ∀ v, Even (G.degree v))
    (P Q : Finset G.Subgraph)
    (hcP : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdP : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hcQ : ∀ H ∈ Q, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdQ : Set.PairwiseDisjoint (Q : Set G.Subgraph) (fun H => H.edgeSet))
    (hcover : (⋃ H ∈ P, H.edgeSet) = ⋃ H ∈ Q, H.edgeSet) : P.card = Q.card := by
  have hle : ∀ P Q : Finset G.Subgraph,
      (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) →
      (∀ H ∈ Q, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      Set.PairwiseDisjoint (Q : Set G.Subgraph) (fun H => H.edgeSet) →
      (⋃ H ∈ P, H.edgeSet) = (⋃ H ∈ Q, H.edgeSet) → P.card ≤ Q.card := by
    intro P Q hcP hdP hcQ hdQ hcover
    have her := even_residual_of_cycle_packing G he P hcP hdP
    obtain ⟨F, hcF, hdF⟩ := even_cycle_decomposition (G \ unionPieces G P) (by
      intro v
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using her v)
    obtain ⟨D, hcD, hdD, hPD, _⟩ := complete_cycle_packing_extension G P hcP hdP F (by
      intro H hH
      refine ⟨(hcF H hH).1, ?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hcF H hH).2 v) hdF
    exact minimum_cycle_subfamily G D hcD hdD
      (fun E hcE hdE => (hi D E hcD hdD hcE hdE).le)
      P Q hPD hcQ hdQ hcover.symm
  exact Nat.le_antisymm (hle P Q hcP hdP hcQ hdQ hcover)
    (hle Q P hcQ hdQ hcP hdP hcover.symm)

lemma HasInvariantCount.allCyclesOptimal {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hi : HasInvariantCount G) (he : ∀ v, Even (G.degree v)) :
    MinimalCounterexample.AllCyclesOptimal G := by
  intro H hcH
  have hcP : ∀ K ∈ ({H} : Finset G.Subgraph),
      K.coe.Connected ∧ K.coe.IsRegularOfDegree 2 := by simpa using hcH
  have hdP : Set.PairwiseDisjoint (({H} : Finset G.Subgraph) : Set G.Subgraph)
      (fun K => K.edgeSet) := by simp
  have her := even_residual_of_cycle_packing G he {H} hcP hdP
  obtain ⟨F, hcF, hdF⟩ := even_cycle_decomposition (G \ unionPieces G {H}) (by
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using her v)
  obtain ⟨D, hcD, hdD, hHD, _⟩ := complete_cycle_packing_extension G {H} hcP hdP F (by
    intro K hK
    refine ⟨(hcF K hK).1, ?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcF K hK).2 v) hdF
  exact ⟨D, hcD, hdD, hHD (Finset.mem_singleton_self H),
    fun E hcE hdE => (hi D E hcD hdD hcE hdE).le⟩

/-- Two edge-disjoint cycles with at least three shared vertices contain a
cycle avoiding any one specified shared vertex. The proof deletes the four
edges incident with that vertex and uses the forest edge bound. -/
lemma two_cycles_have_avoiding_cycle {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H K : G.Subgraph)
    (hcH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hcK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hd : Disjoint H.edgeSet K.edgeSet)
    (hinter : 3 ≤ (H.verts ∩ K.verts).ncard)
    (v : V) (hvH : v ∈ H.verts) (hvK : v ∈ K.verts) :
    ∃ Q : (H.spanningCoe ⊔ K.spanningCoe).Subgraph,
      Q.coe.Connected ∧ Q.coe.IsRegularOfDegree 2 ∧ v ∉ Q.verts := by
  let U := H.spanningCoe ⊔ K.spanningCoe
  let S := H.verts ∪ K.verts
  have hne : H ≠ K := by
    intro h
    obtain ⟨e, he⟩ := cycle_edgeSet_nonempty H hcH.1 hcH.2
    exact Set.disjoint_left.mp hd he (h ▸ he)
  have hdP : Set.PairwiseDisjoint (({H,K} : Finset G.Subgraph) : Set G.Subgraph)
      (fun L => L.edgeSet) := by
    intro A hA B hB hAB
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact (hAB rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hAB rfl).elim
  have hUeq : U = unionPieces G {H,K} := by
    ext a b
    simp [U, unionPieces]
  have hdegH : H.degree v = 2 := by
    have h := hcH.2 ⟨v,hvH⟩
    rw [Subgraph.coe_degree] at h
    simpa only [Subgraph.degree, ← Nat.card_eq_fintype_card] using h
  have hdegK : K.degree v = 2 := by
    have h := hcK.2 ⟨v,hvK⟩
    rw [Subgraph.coe_degree] at h
    simpa only [Subgraph.degree, ← Nat.card_eq_fintype_card] using h
  have hdeg : U.degree v = 4 := by
    have h := unionPieces_degree G {H,K} hdP v
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
    rw [hUeq, h]
    simp [hne, hdegH, hdegK]
  have hcardU : U.edgeSet.ncard = H.verts.ncard + K.verts.ncard := by
    change (H.spanningCoe ⊔ K.spanningCoe).edgeSet.ncard = _
    rw [edgeSet_sup]
    change (H.edgeSet ∪ K.edgeSet).ncard = _
    rw [Set.ncard_union_eq hd, regular_two_edge_vertex_card H hcH.2,
      regular_two_edge_vertex_card K hcK.2]
  have hsize : S.ncard + 3 ≤ U.edgeSet.ncard := by
    have h := Set.ncard_union_add_ncard_inter H.verts K.verts
    change (H.verts ∪ K.verts).ncard + 3 ≤ _
    omega
  have hS : 3 ≤ S.ncard := hinter.trans (Set.ncard_le_ncard
    (show H.verts ∩ K.verts ⊆ S from fun x hx => Or.inl hx.1))
  have hvS : v ∈ S := Or.inl hvH
  let A := U.deleteIncidenceSet v
  have hAS : A.support ⊆ S \ {v} := by
    intro w hw
    obtain ⟨z,hz⟩ := hw
    have hh := deleteIncidenceSet_adj.mp hz
    refine ⟨?_, hh.2.1⟩
    rcases hh.1 with hH | hK
    · exact Or.inl (H.edge_vert hH)
    · exact Or.inr (K.edge_vert hK)
  have hcardA : A.edgeSet.ncard + 4 = U.edgeSet.ncard := by
    have h := U.card_edgeFinset_deleteIncidenceSet v
    simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at h
    change A.edgeSet.ncard = U.edgeSet.ncard - U.degree v at h
    rw [hdeg] at h
    omega
  have hnot : ¬ A.IsAcyclic := by
    intro ha
    have hSv : (S \ {v}).ncard = S.ncard - 1 := Set.ncard_diff_singleton_of_mem hvS
    have hn : (S \ {v}).Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by omega)
    haveI : Nonempty {w : V // w ∈ S \ {v}} := hn.to_subtype
    have hh := forest_edge_card_lt_vertex_card (A.induce (S \ {v})) (ha.induce _)
    have heq := card_edgeFinset_induce_of_support_subset hAS
    simp only [edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hh heq
    omega
  obtain ⟨w,p,hp⟩ : ∃ w, ∃ p : A.Walk w w, p.IsCycle := by
    simpa only [IsAcyclic, not_forall, not_not] using hnot
  have hc := cycle_subgraph_regular A hp
  let Q := promote (U.deleteIncidenceSet_le v) p.toSubgraph
  have hcQ : Q.coe.Connected ∧ Q.coe.IsRegularOfDegree 2 := by
    refine ⟨hc.1, ?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hc.2 x
  refine ⟨Q, hcQ.1, hcQ.2, ?_⟩
  intro hv
  have hv' : v ∈ p.toSubgraph.verts := hv
  have hpos : 0 < p.toSubgraph.coe.degree ⟨v,hv'⟩ := by
    have h := hc.2 ⟨v,hv'⟩
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
    omega
  obtain ⟨z,hz⟩ := (p.toSubgraph.coe.degree_pos_iff_exists_adj ⟨v,hv'⟩).mp hpos
  have hzA : A.Adj v z.val := p.toSubgraph.adj_sub hz
  exact (deleteIncidenceSet_adj.mp hzA).2.1 rfl


lemma degree_at_common_vertex {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H K : G.Subgraph) (hr : H.coe.IsRegularOfDegree 2) (kr : K.coe.IsRegularOfDegree 2)
    (hd : Disjoint H.edgeSet K.edgeSet) (v : V) (hvH : v ∈ H.verts) (hvK : v ∈ K.verts) :
    (H.spanningCoe ⊔ K.spanningCoe).degree v = 4 := by
  have hn : Disjoint (H.neighborSet v) (K.neighborSet v) := by
    apply Set.disjoint_left.mpr
    intro w hwH hwK
    exact Set.disjoint_left.mp hd (show s(v,w) ∈ H.edgeSet from hwH) hwK
  have hH := hr ⟨v,hvH⟩
  have hK := kr ⟨v,hvK⟩
  rw [Subgraph.coe_degree] at hH hK
  simp only [Subgraph.degree, ← Nat.card_eq_fintype_card] at hH hK
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  change (H.neighborSet v ∪ K.neighborSet v).ncard = 4
  rw [Set.ncard_union_eq hn]
  change Nat.card (H.neighborSet v) + Nat.card (K.neighborSet v) = 4
  omega

/-- A pair sharing at least three vertices can be repartitioned into more than
two cycles. This is an INCREASE, not the reduction used in minimum arguments. -/
lemma two_cycles_repartition_more {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H K : G.Subgraph)
    (hcH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hcK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hd : Disjoint H.edgeSet K.edgeSet)
    (hinter : 3 ≤ (H.verts ∩ K.verts).ncard) :
    ∃ F : Finset G.Subgraph,
      (∀ L ∈ F, L.coe.Connected ∧ L.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (F : Set G.Subgraph) (fun L => L.edgeSet) ∧
      (⋃ L ∈ F, L.edgeSet) = H.edgeSet ∪ K.edgeSet ∧ 3 ≤ F.card := by
  obtain ⟨v,hvH,hvK⟩ := (Set.ncard_pos (Set.toFinite _)).mp
    (show 0 < (H.verts ∩ K.verts).ncard by omega)
  let U := H.spanningCoe ⊔ K.spanningCoe
  have hUG : U ≤ G := sup_le H.spanningCoe_le K.spanningCoe_le
  obtain ⟨Q, qc, qr, hvQ⟩ := two_cycles_have_avoiding_cycle H K hcH hcK hd hinter v hvH hvK
  have hcP : ∀ L ∈ ({Q} : Finset U.Subgraph),
      L.coe.Connected ∧ L.coe.IsRegularOfDegree 2 := by
    intro L hL
    have h := Finset.mem_singleton.mp hL
    subst L
    refine ⟨qc, ?_⟩
    intro w
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using qr w
  have hdP : Set.PairwiseDisjoint (({Q} : Finset U.Subgraph) : Set U.Subgraph)
      (fun L => L.edgeSet) := by simp
  have heU := even_union_two_cycle_pieces H K hcH.2 hcK.2 hd
  have her := even_residual_of_cycle_packing U (by
    intro w
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heU w)
    {Q} (by
      intro L hL
      refine ⟨(hcP L hL).1, ?_⟩
      intro w
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hcP L hL).2 w) hdP
  obtain ⟨R, hcR, hdR⟩ := even_cycle_decomposition (U \ unionPieces U {Q}) (by
    intro w
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using her w)
  obtain ⟨D, hcD, hdD, hQD, _⟩ := complete_cycle_packing_extension U {Q} (by
    intro L hL
    refine ⟨(hcP L hL).1, ?_⟩
    intro w
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcP L hL).2 w) hdP R (by
    intro L hL
    refine ⟨(hcR L hL).1, ?_⟩
    intro w
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcR L hL).2 w) hdR
  have hmemQ : Q ∈ D := hQD (Finset.mem_singleton_self Q)
  have hdeg := degree_at_common_vertex H K hcH.2 hcK.2 hd v hvH hvK
  have hcount := cycle_decomposition_vertex_count U D hcD hdD v
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdeg hcount
  have hdegU : Nat.card (U.neighborSet v) = 4 := hdeg
  change 2 * (D.filter (fun L => v ∈ L.verts)).card = Nat.card (U.neighborSet v) at hcount
  rw [hdegU] at hcount
  have hsub : D.filter (fun L => v ∈ L.verts) ⊆ D.erase Q := by
    intro L hL
    obtain ⟨hLD,hvL⟩ := Finset.mem_filter.mp hL
    exact Finset.mem_erase.mpr ⟨fun h => hvQ (h ▸ hvL), hLD⟩
  have hle := Finset.card_le_card hsub
  have herase := Finset.card_erase_of_mem hmemQ
  have hDcard : 3 ≤ D.card := by omega
  let F := D.image (promote hUG)
  have hFcard : F.card = D.card := Finset.card_image_of_injective D (promote_injective hUG)
  refine ⟨F, ?_, ?_, ?_, by omega⟩
  · intro L hL
    obtain ⟨M,hM,rfl⟩ := Finset.mem_image.mp hL
    refine ⟨(hcD M hM).1, ?_⟩
    intro w
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcD M hM).2 w
  · intro L hL M hM hne
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hM
    exact hdD.1 hA hB (fun h => hne (congrArg (promote hUG) h))
  · have hh : (⋃ L ∈ F, L.edgeSet) = U.edgeSet := by
      rw [← hdD.2]
      ext e
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨L,hL,heL⟩
        obtain ⟨M,hM,rfl⟩ := Finset.mem_image.mp hL
        exact ⟨M,hM,heL⟩
      · rintro ⟨M,hM,heM⟩
        exact ⟨promote hUG M,Finset.mem_image.mpr ⟨M,hM,rfl⟩,heM⟩
    exact hh.trans (by simp only [U,edgeSet_sup]; rfl)

/-- In an even graph with invariant partition count, any two edge-disjoint
cycles share at most two vertices. This quantifies over all packings, not only
one chosen decomposition. -/
lemma HasInvariantCount.intersection_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hi : HasInvariantCount G) (he : ∀ v, Even (G.degree v))
    (H K : G.Subgraph)
    (hcH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hcK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hd : Disjoint H.edgeSet K.edgeSet) : (H.verts ∩ K.verts).ncard ≤ 2 := by
  by_contra! hgt
  obtain ⟨F,hcF,hdF,hcover,hcard⟩ := two_cycles_repartition_more H K hcH hcK hd hgt
  have hne : H ≠ K := by
    intro h
    obtain ⟨e,he⟩ := cycle_edgeSet_nonempty H hcH.1 hcH.2
    exact Set.disjoint_left.mp hd he (h ▸ he)
  have hcP : ∀ L ∈ ({H,K} : Finset G.Subgraph),
      L.coe.Connected ∧ L.coe.IsRegularOfDegree 2 := by
    intro L hL
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact hcH
    · exact Finset.mem_singleton.mp hL ▸ hcK
  have hdP : Set.PairwiseDisjoint (({H,K} : Finset G.Subgraph) : Set G.Subgraph)
      (fun L => L.edgeSet) := by
    intro A hA B hB hAB
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact (hAB rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hAB rfl).elim
  have hcov : (⋃ L ∈ ({H,K} : Finset G.Subgraph), L.edgeSet) = ⋃ L ∈ F, L.edgeSet := by
    rw [hcover]
    simp
  have h := hi.packing_card_eq he {H,K} F hcP hdP hcF hdF hcov
  rw [Finset.card_pair hne] at h
  omega

end InvariantPartitions
end Erdos184
