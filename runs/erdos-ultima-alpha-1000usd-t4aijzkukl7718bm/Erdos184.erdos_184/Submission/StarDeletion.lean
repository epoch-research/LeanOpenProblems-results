import Submission.MatchingDeletion

/-! Deletion of an independent-leaf star forest from an even graph.
These are quantitative auxiliary inequalities, not a linear upper bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.StarDeletion
open Critical MaximumCycles Subfamilies
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 10000
variable {V : Type*} [Fintype V]

lemma even_number_outside_two {G M : SimpleGraph V}
    (hG : ∀ v, Even (Nat.card (G.neighborSet v)))
    (hcycle : ∀ H : G.Subgraph, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 →
      2 ≤ (H.spanningCoe \ M).edgeFinset.card) :
    2 * number G ≤ (G \ M).edgeFinset.card := by
  obtain ⟨D,hD,hdec,hcard⟩ := Rigidity.minimum_cycles (G := G) (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hG)
  let A (H : G.Subgraph) := H.spanningCoe.edgeFinset \ M.edgeFinset
  have ha (H : G.Subgraph) (hH : H ∈ D) : 2 ≤ (A H).card := by
    have hh := hcycle H (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hD H hH)
    simpa only [SimpleGraph.edgeFinset_sdiff] using hh
  have hp : (D : Set G.Subgraph).PairwiseDisjoint A := by
    intro H hH K hK hne
    apply Finset.disjoint_left.mpr
    intro e heH heK
    exact Set.disjoint_left.mp (hdec.1 hH hK hne)
      (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp heH).1)
      (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp heK).1)
  have hu : D.biUnion A = (G \ M).edgeFinset := by
    ext e
    simp only [Finset.mem_biUnion,A,Finset.mem_sdiff,SimpleGraph.mem_edgeFinset,
      SimpleGraph.edgeSet_sdiff,Set.mem_diff]
    have hh := Set.ext_iff.mp hdec.2 e
    simp only [Set.mem_iUnion,exists_prop] at hh
    change (∃ H ∈ D, e ∈ H.edgeSet ∧ e ∉ M.edgeSet) ↔ e ∈ G.edgeSet ∧ e ∉ M.edgeSet
    constructor
    · rintro ⟨H,hHD,heH,hn⟩
      exact ⟨hh.mp ⟨H,hHD,heH⟩,hn⟩
    · rintro ⟨heG,hn⟩
      obtain ⟨H,hHD,heH⟩ := hh.mpr heG
      exact ⟨H,hHD,heH,hn⟩
  have hs := Finset.sum_le_sum (s := D) (fun H hH => ha H hH)
  rw [← Finset.card_biUnion hp,hu] at hs
  simpa only [Finset.sum_const,smul_eq_mul,mul_comm,hcard] using hs


lemma delete_with_repair {G M : SimpleGraph V} {b : ℕ} (hMG : M ≤ G)
    (hG : ∀ v, Even (Nat.card (G.neighborSet v)))
    (hrepair : ∀ T : SimpleGraph V, T ≤ G →
      (∀ v, Even (Nat.card (T.neighborSet v))) → 2 * number T ≤ (T \ M).edgeFinset.card)
    (hlower : ∀ D : Finset (G \ M).Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) → IsDecomposition (G \ M) D →
      b ≤ (edgePieces D).card) :
    2 * number G + b ≤ 2 * number (G \ M) := by
  let R := G \ M
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum R
  let E := edgePieces D
  let C := D \ E
  let F := subfamilyGraph E
  let K := subfamilyGraph C
  let T := F ⊔ M
  have hED : E ⊆ D := Finset.filter_subset _ _
  have hCD : C ⊆ D := Finset.sdiff_subset
  have hFR : F ≤ R := subfamilyGraph_le _
  have hKR : K ≤ R := subfamilyGraph_le _
  have hdis : Disjoint K.edgeSet F.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heK heF
    rw [subfamilyGraph_edges] at heK heF
    obtain ⟨H,hHC,heH⟩ := Set.mem_iUnion₂.mp heK
    obtain ⟨J,hJE,heJ⟩ := Set.mem_iUnion₂.mp heF
    have hne : H ≠ J := fun hh => (Finset.mem_sdiff.mp hHC).2 (hh ▸ hJE)
    exact Set.disjoint_left.mp (hdec.1 (hCD hHC) (hED hJE) hne) heH heJ
  have hdecomp : K ⊔ F = R := by
    apply SimpleGraph.edgeSet_injective
    rw [SimpleGraph.edgeSet_sup,subfamilyGraph_edges,subfamilyGraph_edges,← hdec.2]
    ext e
    simp only [Set.mem_union,Set.mem_iUnion,exists_prop,C,Finset.mem_sdiff]
    constructor
    · rintro (⟨H,hH,he⟩ | ⟨H,hH,he⟩)
      · exact ⟨H,hH.1,he⟩
      · exact ⟨H,hED hH,he⟩
    · rintro ⟨H,hHD,he⟩
      by_cases hH : H ∈ E
      · exact Or.inr ⟨H,hH,he⟩
      · exact Or.inl ⟨H,⟨hHD,hH⟩,he⟩
  have hTM : T \ M = F := by
    ext x y
    have hh : F.Adj x y → ¬ M.Adj x y := fun h => (hFR h).2
    change (F.Adj x y ∨ M.Adj x y) ∧ ¬ M.Adj x y ↔ F.Adj x y
    tauto
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
  have hTe : ∀ v, Even (Nat.card (T.neighborSet v)) := by
    intro v
    have hp := edgePieces_degree_parity D hD hdec v
    have hh := degree_sdiff_add G M hMG v
    have hs := Vertex.degree_sup_inf F M v
    have hbot : F ⊓ M = ⊥ := by
      ext x y
      exact ⟨fun h => (hFR h.1).2 h.2,False.elim⟩
    have he := hG v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hs
    rw [hbot] at hs
    have hz : (⊥ : SimpleGraph V).degree v = 0 := by simp
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hp hh hs he hz ⊢
    change Even (Nat.card (F.neighborSet v)) ↔ Even (Nat.card (R.neighborSet v)) at hp
    change Even (Nat.card (T.neighborSet v))
    simp only [Nat.even_iff] at hp he ⊢
    change Nat.card (R.neighborSet v) + Nat.card (M.neighborSet v) = Nat.card (G.neighborSet v) at hh
    change Nat.card (T.neighborSet v) + Nat.card ((⊥ : SimpleGraph V).neighborSet v) = Nat.card (F.neighborSet v) + Nat.card (M.neighborSet v) at hs
    omega
  have hTG : T ≤ G := sup_le (hFR.trans sdiff_le) hMG
  have hb := hrepair T hTG hTe
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hb
  rw [hTM] at hb
  have hFcard := edgePieces_graph_card D hdec
  have hKnum := minimal_subfamily_number D hD hdec hcard C hCD
  have hsum : C.card + E.card = D.card := Finset.card_sdiff_add_card_eq_card hED
  have hsingle := hlower D hD hdec
  have hn := CycleForestCertificate.number_sup_le hdisKT
  rw [htotal] at hn
  change number K = C.card at hKnum
  change F.edgeFinset.card = E.card at hFcard
  change b ≤ E.card at hsingle
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hFcard hsingle ⊢
  dsimp only [R] at hcard
  omega


lemma independent_cover_degree_sum (G : SimpleGraph V) (B : Finset V)
    (hB : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v)
    (hcover : ∀ u v, G.Adj u v → u ∈ B ∨ v ∈ B) :
    (∑ v ∈ B, G.degree v) = G.edgeFinset.card := by
  have hp : (B : Set V).PairwiseDisjoint (fun v => G.incidenceFinset v) := by
    intro u hu v hv huv
    apply Finset.disjoint_left.mpr
    intro e he hu'
    exact hB u hu v hv (G.adj_of_mem_incidenceSet huv
      ((G.mem_incidenceFinset u e).mp he) ((G.mem_incidenceFinset v e).mp hu'))
  have heq : B.biUnion (fun v => G.incidenceFinset v) = G.edgeFinset := by
    ext e
    constructor
    · intro he
      obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp he
      exact G.incidenceFinset_subset v hv
    · intro he
      induction e using Sym2.ind with | h u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      rcases hcover u v huv with hu | hv
      · exact Finset.mem_biUnion.mpr ⟨u,hu,(G.mem_incidenceFinset u s(u,v)).mpr ⟨huv,by simp⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨v,hv,(G.mem_incidenceFinset v s(u,v)).mpr ⟨huv,by simp⟩⟩
  have hc := congrArg Finset.card heq
  rw [Finset.card_biUnion hp] at hc
  simpa only [SimpleGraph.card_incidenceFinset_eq_degree] using hc

lemma cycle_outside_stars_two {G M : SimpleGraph V} (B : Finset V)
    (hB : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v)
    (hcover : ∀ u v, M.Adj u v → u ∈ B ∨ v ∈ B)
    (hdeg : ∀ v ∈ B, Nat.card (M.neighborSet v) ≤ 1)
    (H : G.Subgraph) (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    2 ≤ (H.spanningCoe \ M).edgeFinset.card := by
  let C := H.spanningCoe
  let N := C ⊓ M
  let R := C \ M
  have hNC : N ≤ C := inf_le_left
  have hNM : N ≤ M := inf_le_right
  have hCN : C \ N = R := by
    ext x y
    change C.Adj x y ∧ ¬ (C.Adj x y ∧ M.Adj x y) ↔ C.Adj x y ∧ ¬ M.Adj x y
    tauto
  have hNcard := independent_cover_degree_sum N B
    (fun u hu v hv huv => hB u hu v hv (H.spanningCoe_le (hNC huv)))
    (fun u v huv => hcover u v (hNM huv))
  have hRcard := ParityDegreeLower.independent_degree_sum_le R B
    (fun u hu v hv huv => hB u hu v hv (H.spanningCoe_le huv.1))
  have hdegrees (v : V) (hv : v ∈ B) :
      Nat.card (N.neighborSet v) ≤ Nat.card (R.neighborSet v) := by
    have hd := degree_sdiff_add C N hNC v
    have hn := SimpleGraph.degree_le_of_le (v := v) hNM
    have hnc := SimpleGraph.degree_le_of_le (v := v) hNC
    have hc := regular_two_spanning_degree H hH.2 v
    have hm := hdeg v hv
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hn hnc hc
    rw [hCN] at hd
    change Nat.card (C.neighborSet v) = _ at hc
    split_ifs at hc <;> omega
  have hs := Finset.sum_le_sum (s := B) (fun v hv => hdegrees v hv)
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hNcard hRcard
  rw [hNcard] at hs
  have hle := hs.trans hRcard
  have hsum : R.edgeFinset.card + N.edgeFinset.card = C.edgeFinset.card := by
    simp only [R,N,SimpleGraph.edgeFinset_sdiff,SimpleGraph.edgeFinset_inf]
    exact Finset.card_sdiff_add_card_inter _ _
  obtain ⟨v⟩ := hH.1.nonempty
  obtain ⟨p,hp,hpH⟩ := LongRing.regular_cycle_walk_at H hH.1 hH.2 v.val v.property
  have hpc := cycle_edge_count G hp
  have hpl := hp.three_le_length
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hle hsum hpc ⊢
  rw [hpH] at hpc
  change Nat.card C.edgeSet = _ at hpc
  change 2 ≤ Nat.card R.edgeSet
  omega

lemma delete_stars_number {G M : SimpleGraph V} (hMG : M ≤ G)
    (hG : ∀ v, Even (Nat.card (G.neighborSet v))) (B : Finset V)
    (hB : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v)
    (hcover : ∀ u v, M.Adj u v → u ∈ B ∨ v ∈ B)
    (hdeg : ∀ v ∈ B, Nat.card (M.neighborSet v) = 1) :
    2 * number G + B.card ≤ 2 * number (G \ M) := by
  apply delete_with_repair hMG hG
  · intro T hTG hT
    apply even_number_outside_two hT
    intro H hH
    exact cycle_outside_stars_two B
      (fun u hu v hv huv => hB u hu v hv (hTG huv)) hcover
      (fun v hv => (hdeg v hv).le) H hH
  · intro D hD hdec
    apply ParityDegreeLower.independent_odd_le_singletons D hD hdec B
      (fun u hu v hv huv => hB u hu v hv huv.1)
    intro v hv
    have hd := degree_sdiff_add G M hMG v
    have he := hG v
    have hm := hdeg v hv
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd ⊢
    rw [Nat.even_iff] at he
    rw [Nat.odd_iff]
    omega

lemma hull_stars_boost {G M : SimpleGraph V} (hMG : M ≤ G)
    (hG : ∀ v, Even (Nat.card (G.neighborSet v))) (B : Finset V)
    (hB : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v)
    (hcover : ∀ u v, M.Adj u v → u ∈ B ∨ v ∈ B)
    (hdeg : ∀ v ∈ B, Nat.card (M.neighborSet v) = 1) :
    2 * number G + B.card ≤ 2 * EdgeHull.value G := by
  have h := delete_stars_number hMG hG B hB hcover hdeg
  have hh := EdgeHull.le_value (sdiff_le : G \ M ≤ G)
  omega

end Erdos184Work.StarDeletion
#print axioms Erdos184Work.StarDeletion.delete_with_repair
#print axioms Erdos184Work.StarDeletion.hull_stars_boost
