import Submission.StarDeletion

/-! Exact edge-deletion formula for even graphs. This is a local identity,
not a uniform bound on cycle-and-edge decompositions. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ExactEdgeDeletion
open Critical MaximumCycles Subfamilies
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 10000
variable {V : Type*} [Fintype V]

lemma cycle_upper_bound {G : SimpleGraph V} {a b u : V}
    (p : G.Walk u u) (hp : p.IsCycle) (he : p.toSubgraph.Adj a b) :
    number (G.deleteEdges {s(a,b)}) + 1 ≤
      number (G \ p.toSubgraph.spanningCoe) + p.length := by
  let C := p.toSubgraph.spanningCoe
  let K := G \ C
  let F := C.deleteEdges {s(a,b)}
  have hU : K ⊔ F = G.deleteEdges {s(a,b)} := by
    ext x y
    change (G.Adj x y ∧ ¬ C.Adj x y) ∨ F.Adj x y ↔ _
    simp only [F,SimpleGraph.deleteEdges_adj]
    have hCG : C.Adj x y → G.Adj x y := p.toSubgraph.adj_sub
    have hab : s(a,b) ∈ C.edgeSet := he
    have hnot : ¬ C.Adj x y → s(x,y) ∉ ({s(a,b)} : Set (Sym2 V)) := by
      intro hn heq
      exact hn (show s(x,y) ∈ C.edgeSet from (Set.mem_singleton_iff.mp heq).symm ▸ hab)
    change (G.Adj x y ∧ ¬ C.Adj x y) ∨
        (C.Adj x y ∧ s(x,y) ∉ ({s(a,b)} : Set (Sym2 V))) ↔ _
    tauto
  have hd : Disjoint K.edgeSet F.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heK heF
    rw [SimpleGraph.edgeSet_sdiff] at heK
    rw [SimpleGraph.edgeSet_deleteEdges] at heF
    exact heK.2 heF.1
  have hn := CycleForestCertificate.number_sup_le hd
  have hf := number_le_edges F
  have hc : F.edgeFinset.card + 1 = p.length := by
    have hcount := cycle_edge_count G hp
    have heC : s(a,b) ∈ C.edgeFinset := SimpleGraph.mem_edgeFinset.mpr he
    have hfin : F.edgeFinset = C.edgeFinset.erase s(a,b) := by
      ext e
      simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.edgeSet_deleteEdges,
        Finset.mem_erase,Set.mem_diff,Set.mem_singleton_iff,F]
      tauto
    rw [hfin,Finset.card_erase_add_one heC]
    exact hcount
  rw [hU] at hn
  change number (G.deleteEdges {s(a,b)}) + 1 ≤ number K + p.length
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hf hc
  omega

lemma attaining_cycle {G : SimpleGraph V} (heven : ∀ v, Even (G.degree v))
    {a b : V} (hab : G.Adj a b) :
    ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.toSubgraph.Adj a b ∧
      number (G.deleteEdges {s(a,b)}) + 1 =
        number (G \ p.toSubgraph.spanningCoe) + p.length := by
  let M := SimpleGraph.edge a b
  let R := G \ M
  have hMG : M ≤ G := (SimpleGraph.edge_le_iff G).mpr (Or.inr hab)
  have habM : M.Adj a b := (SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab.ne⟩
  have hMe : M.edgeSet = {s(a,b)} := SimpleGraph.edge_edgeSet_of_ne hab.ne
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum R
  let E := edgePieces D
  let A := D \ E
  let F := subfamilyGraph E
  let K := subfamilyGraph A
  let T := F ⊔ M
  have hED : E ⊆ D := Finset.filter_subset _ _
  have hAD : A ⊆ D := Finset.sdiff_subset
  have hFR : F ≤ R := subfamilyGraph_le _
  have hKR : K ≤ R := subfamilyGraph_le _
  have hdis : Disjoint K.edgeSet F.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heK heF
    rw [subfamilyGraph_edges] at heK heF
    obtain ⟨H,hHA,heH⟩ := Set.mem_iUnion₂.mp heK
    obtain ⟨J,hJE,heJ⟩ := Set.mem_iUnion₂.mp heF
    have hne : H ≠ J := fun hh => (Finset.mem_sdiff.mp hHA).2 (hh ▸ hJE)
    exact Set.disjoint_left.mp (hdec.1 (hAD hHA) (hED hJE) hne) heH heJ
  have hdecomp : K ⊔ F = R := by
    apply SimpleGraph.edgeSet_injective
    rw [SimpleGraph.edgeSet_sup,subfamilyGraph_edges,subfamilyGraph_edges,← hdec.2]
    ext e
    simp only [Set.mem_union,Set.mem_iUnion,exists_prop,A,Finset.mem_sdiff]
    constructor
    · rintro (⟨H,hH,he⟩ | ⟨H,hH,he⟩)
      · exact ⟨H,hH.1,he⟩
      · exact ⟨H,hED hH,he⟩
    · rintro ⟨H,hHD,he⟩
      by_cases hH : H ∈ E
      · exact Or.inr ⟨H,hH,he⟩
      · exact Or.inl ⟨H,⟨hHD,hH⟩,he⟩
  have hKG : K ≤ G := hKR.trans sdiff_le
  have htotal : K ⊔ T = G := by
    rw [show K ⊔ T = (K ⊔ F) ⊔ M by exact (sup_assoc _ _ _).symm,hdecomp]
    exact sdiff_sup_cancel hMG
  have hdisKT : Disjoint K.edgeSet T.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heK heT
    change e ∈ (F ⊔ M).edgeSet at heT
    rw [SimpleGraph.edgeSet_sup] at heT
    rcases heT with heF | heM
    · exact Set.disjoint_left.mp hdis heK heF
    · have hh := SimpleGraph.edgeSet_mono hKR heK
      change e ∈ (G \ M).edgeSet at hh
      rw [SimpleGraph.edgeSet_sdiff] at hh
      exact hh.2 heM
  have hTK : T = G \ K := by
    rw [← htotal,sup_sdiff,sdiff_self,bot_sup_eq]
    exact (sdiff_eq_left.mpr (SimpleGraph.disjoint_edgeSet.mp hdisKT.symm)).symm
  have hKT : K = G \ T := by
    rw [← htotal,sup_sdiff,sdiff_self,sup_bot_eq]
    exact (sdiff_eq_left.mpr (SimpleGraph.disjoint_edgeSet.mp hdisKT)).symm
  have hTe : ∀ v, Even (Nat.card (T.neighborSet v)) := by
    intro v
    have hp := edgePieces_degree_parity D hD hdec v
    have hh := degree_sdiff_add G M hMG v
    have hs := Vertex.degree_sup_inf F M v
    have hbot : F ⊓ M = ⊥ := by
      ext x y
      exact ⟨fun h => (hFR h.1).2 h.2,False.elim⟩
    have he := heven v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hs
    rw [hbot] at hs
    have hz : (⊥ : SimpleGraph V).degree v = 0 := by simp
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hp hh hs he hz ⊢
    change Even (Nat.card (F.neighborSet v)) ↔ Even (Nat.card (R.neighborSet v)) at hp
    simp only [Nat.even_iff] at hp he ⊢
    change Nat.card (R.neighborSet v) + Nat.card (M.neighborSet v) = Nat.card (G.neighborSet v) at hh
    change Nat.card (T.neighborSet v) + Nat.card ((⊥ : SimpleGraph V).neighborSet v) = Nat.card (F.neighborSet v) + Nat.card (M.neighborSet v) at hs
    omega
  have hTF : T \ F = M := by
    have hMF : Disjoint M F := by
      apply SimpleGraph.disjoint_edgeSet.mp
      apply Set.disjoint_left.mpr
      intro e heM heF
      have hh := SimpleGraph.edgeSet_mono hFR heF
      rw [SimpleGraph.edgeSet_sdiff] at hh
      exact hh.2 heM
    exact sup_sdiff_left_self.trans (sdiff_eq_left.mpr hMF)
  have hFacyc : F.IsAcyclic := minimal_edge_pieces_acyclic D hD hdec hcard
  obtain ⟨B,hB,hdecB,hcB⟩ := SingleAddition.even_feedback_decomposition T F (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hTe) hFacyc
  have hmcard : M.edgeFinset.card = 1 := by
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card]
    rw [hMe]
    simp
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hcB hmcard
  rw [hTF,hmcard] at hcB
  have habT : T.Adj a b := Or.inr habM
  have hBne : B.Nonempty := by
    have he : s(a,b) ∈ ⋃ H ∈ B, H.edgeSet := hdecB.2.symm ▸ habT
    obtain ⟨H,hH,_⟩ := Set.mem_iUnion₂.mp he
    exact ⟨H,hH⟩
  have hBpos : 0 < B.card := Finset.card_pos.mpr hBne
  obtain ⟨H,rfl⟩ := Finset.card_eq_one.mp (by omega : B.card = 1)
  have hH := hB H (Finset.mem_singleton_self _)
  have hHT : H.spanningCoe = T := by
    apply SimpleGraph.edgeSet_injective
    simpa only [Finset.set_biUnion_singleton] using hdecB.2
  have haH : a ∈ H.verts := H.edge_vert (hHT.symm ▸ habT)
  obtain ⟨q,hq,hqH⟩ := LongRing.regular_cycle_walk_at H hH.1 hH.2 a haH
  have hTG : T ≤ G := sup_le (hFR.trans sdiff_le) hMG
  let p := q.mapLe hTG
  have hp : p.IsCycle := hq.mapLe hTG
  have hpT : p.toSubgraph.spanningCoe = T := by
    rw [← hHT,← hqH]
    ext x y
    exact Walk.adj_toSubgraph_mapLe hTG
  have hpe : p.toSubgraph.Adj a b := by
    change p.toSubgraph.spanningCoe.Adj a b
    rw [hpT]
    exact habT
  have hlen : p.length = F.edgeFinset.card + 1 := by
    have hh := cycle_edge_count G hp
    have hc := SimpleGraph.card_edgeFinset_sup_edge (G := F) (s := a) (t := b)
      (fun h => (hFR h).2 habM) hab.ne
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hh hc ⊢
    rw [hpT] at hh
    exact hh.symm.trans hc
  have hFcard := edgePieces_graph_card D hdec
  have hKnum := minimal_subfamily_number D hD hdec hcard A hAD
  have hsum : A.card + E.card = D.card := Finset.card_sdiff_add_card_eq_card hED
  change number K = A.card at hKnum
  change F.edgeFinset.card = E.card at hFcard
  refine ⟨a,p,hp,hpe,?_⟩
  rw [hpT,← hKT,hlen]
  change number R + 1 = _
  omega

/-- In a cycle-critical even graph, an attaining cycle is shortest among the
cycles containing the specified edge. -/
lemma shortest_attaining_cycle {G : SimpleGraph V}
    (heven : ∀ v, Even (G.degree v)) (hcrit : EvenCore.CycleCritical G)
    {a b : V} (hab : G.Adj a b) :
    ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.toSubgraph.Adj a b ∧
      (∀ (v : V) (q : G.Walk v v), q.IsCycle → q.toSubgraph.Adj a b →
        p.length ≤ q.length) ∧
      number (G.deleteEdges {s(a,b)}) + 2 = number G + p.length := by
  obtain ⟨u,p,hp,hpe,heq⟩ := attaining_cycle heven hab
  have hc := hcrit u p hp
  refine ⟨u,p,hp,hpe,?_,by omega⟩
  intro v q hq hqe
  have hu := cycle_upper_bound q hq hqe
  have hcq := hcrit v q hq
  omega

/-- The exact formula uses edge-local girth, not the shortest cycle elsewhere
in the graph. The shortest-cycle hypothesis is therefore explicitly local. -/
lemma shortest_cycle_formula {G : SimpleGraph V}
    (heven : ∀ v, Even (G.degree v)) (hcrit : EvenCore.CycleCritical G)
    {a b u : V} (p : G.Walk u u) (hp : p.IsCycle) (hpe : p.toSubgraph.Adj a b)
    (hshort : ∀ (v : V) (q : G.Walk v v), q.IsCycle → q.toSubgraph.Adj a b →
      p.length ≤ q.length) :
    number (G.deleteEdges {s(a,b)}) + 2 = number G + p.length := by
  obtain ⟨v,q,hq,hqe,hqshort,heq⟩ := shortest_attaining_cycle heven hcrit (p.toSubgraph.adj_sub hpe)
  have h1 := hshort v q hq hqe
  have h2 := hqshort u p hp hpe
  omega

lemma even_minimal_shortest_cycle_formula {G : SimpleGraph V}
    (heven : ∀ v, Even (G.degree v)) (hmin : EvenCore.EvenMinimal G)
    {a b u : V} (p : G.Walk u u) (hp : p.IsCycle) (hpe : p.toSubgraph.Adj a b)
    (hshort : ∀ (v : V) (q : G.Walk v v), q.IsCycle → q.toSubgraph.Adj a b →
      p.length ≤ q.length) :
    number (G.deleteEdges {s(a,b)}) + 2 = number G + p.length :=
  shortest_cycle_formula heven (hmin.cycleCritical heven) p hp hpe hshort

end Erdos184Work.ExactEdgeDeletion
#print axioms Erdos184Work.ExactEdgeDeletion.attaining_cycle
#print axioms Erdos184Work.ExactEdgeDeletion.cycle_upper_bound
#print axioms Erdos184Work.ExactEdgeDeletion.shortest_attaining_cycle
#print axioms Erdos184Work.ExactEdgeDeletion.even_minimal_shortest_cycle_formula
