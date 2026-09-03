import Submission.CycleForestCertificate
import Submission.ParityDegreeLower

/-! Quantitative increase on deleting a matching from an even graph.
This is an auxiliary inequality, not a uniform upper decomposition bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.MatchingDeletion
open Critical MaximumCycles Subfamilies
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 10000
variable {V : Type*} [Fintype V]

lemma cycle_outside_matching_two {G M : SimpleGraph V}
    (hM : ∀ v, Nat.card (M.neighborSet v) ≤ 1) (H : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    2 ≤ (H.spanningCoe \ M).edgeFinset.card := by
  let N := H.spanningCoe ⊓ M
  have hd (v : V) : Nat.card (N.neighborSet v) ≤ if v ∈ H.verts then 1 else 0 := by
    by_cases hv : v ∈ H.verts
    · rw [if_pos hv]
      have hn := SimpleGraph.degree_le_of_le (v := v) (inf_le_right : N ≤ M)
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hn
      exact hn.trans (hM v)
    · rw [if_neg hv]
      have he := regular_two_spanning_degree H (by
        simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hH.2) v
      rw [if_neg hv] at he
      have hn := SimpleGraph.degree_le_of_le (v := v) (inf_le_left : N ≤ H.spanningCoe)
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at he hn
      exact hn.trans he.le
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hd v)
  have hsum := N.sum_degrees_eq_twice_card_edges
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hsum
  rw [hsum] at hs
  have hi : (∑ v : V, if v ∈ H.verts then 1 else 0) = H.verts.ncard := by
    rw [Set.ncard_eq_toFinset_card']
    simp [Set.toFinset]
  rw [hi] at hs
  have hc := regular_two_card_edges H (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hH.2)
  have hadd : (H.spanningCoe \ M).edgeFinset.card + N.edgeFinset.card = H.spanningCoe.edgeFinset.card := by
    simp only [SimpleGraph.edgeFinset_sdiff,SimpleGraph.edgeFinset_inf,N]
    exact Finset.card_sdiff_add_card_inter _ _
  obtain ⟨v⟩ := hH.1.nonempty
  obtain ⟨p,hp,hpH⟩ := LongRing.regular_cycle_walk_at H hH.1 (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hH.2) v.val v.property
  have hpCard := cycle_edge_count G hp
  have hpLen := hp.three_le_length
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hs hc hadd hpCard ⊢
  rw [hpH] at hpCard
  omega

lemma even_number_outside_matching {G M : SimpleGraph V}
    (hG : ∀ v, Even (Nat.card (G.neighborSet v))) (hM : ∀ v, Nat.card (M.neighborSet v) ≤ 1) :
    2 * number G ≤ (G \ M).edgeFinset.card := by
  obtain ⟨D,hD,hdec,hcard⟩ := Rigidity.minimum_cycles (G := G) (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hG)
  let A (H : G.Subgraph) := H.spanningCoe.edgeFinset \ M.edgeFinset
  have ha (H : G.Subgraph) (hH : H ∈ D) : 2 ≤ (A H).card := by
    have hh := cycle_outside_matching_two hM H (by
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

lemma matching_edges_le_singletons {G M : SimpleGraph V} (hMG : M ≤ G)
    (hG : ∀ v, Even (Nat.card (G.neighborSet v))) (hM : ∀ v, Nat.card (M.neighborSet v) ≤ 1)
    (D : Finset (G \ M).Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition (G \ M) D) : M.edgeFinset.card ≤ (edgePieces D).card := by
  let F := subfamilyGraph (edgePieces D)
  have hd (v : V) : Nat.card (M.neighborSet v) ≤ Nat.card (F.neighborSet v) := by
    by_cases hm : Nat.card (M.neighborSet v) = 0
    · rw [hm]; exact Nat.zero_le _
    · have hdM : Nat.card (M.neighborSet v) = 1 := by have := hM v; omega
      have he := hG v
      have hh := degree_sdiff_add G M hMG v
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh
      have ho : Odd (Nat.card ((G \ M).neighborSet v)) := by
        rw [Nat.even_iff] at he
        rw [Nat.odd_iff]
        omega
      rw [hdM]
      have hf := ParityDegreeLower.singleton_degree_pos D hD hdec (v := v) (by
        simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using ho)
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hf
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hd v)
  have hm := M.sum_degrees_eq_twice_card_edges
  have hf := F.sum_degrees_eq_twice_card_edges
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hm hf
  rw [hm,hf] at hs
  have hc := edgePieces_graph_card D hdec
  change F.edgeFinset.card = _ at hc
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hs hc ⊢
  omega

lemma delete_matching_number {G M : SimpleGraph V} (hMG : M ≤ G)
    (hG : ∀ v, Even (Nat.card (G.neighborSet v))) (hM : ∀ v, Nat.card (M.neighborSet v) ≤ 1) :
    2 * number G + M.edgeFinset.card ≤ 2 * number (G \ M) := by
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
  have hb := even_number_outside_matching hTe hM
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hb
  rw [hTM] at hb
  have hFcard := edgePieces_graph_card D hdec
  have hKnum := minimal_subfamily_number D hD hdec hcard C hCD
  have hsum : C.card + E.card = D.card := Finset.card_sdiff_add_card_eq_card hED
  have hsingle := matching_edges_le_singletons hMG hG hM D hD hdec
  have hn := CycleForestCertificate.number_sup_le hdisKT
  rw [htotal] at hn
  change number K = C.card at hKnum
  change F.edgeFinset.card = E.card at hFcard
  change M.edgeFinset.card ≤ E.card at hsingle
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hFcard hsingle ⊢
  dsimp only [R] at hcard
  omega

/-- The arbitrary-edge hull of an even graph is raised by at least half the
size of any matching it contains. -/
lemma hull_matching_boost {G M : SimpleGraph V} (hMG : M ≤ G)
    (hG : ∀ v, Even (Nat.card (G.neighborSet v)))
    (hM : ∀ v, Nat.card (M.neighborSet v) ≤ 1) :
    2 * number G + M.edgeFinset.card ≤ 2 * EdgeHull.value G := by
  have h := delete_matching_number hMG hG hM
  have hh := EdgeHull.le_value (sdiff_le : G \ M ≤ G)
  omega

/-- A proper even subgraph of a globally minimal graph cannot contain a large
matching unless its decomposition number is correspondingly below the ambient
number. This does not assert that the gap is a fixed fraction of that number. -/
lemma minimal_even_matching_gap {G E M : SimpleGraph V}
    (hm : EdgeHull.Minimal G) (hEG : E ≤ G) (hne : E ≠ G) (hME : M ≤ E)
    (hE : ∀ v, Even (Nat.card (E.neighborSet v)))
    (hM : ∀ v, Nat.card (M.neighborSet v) ≤ 1) :
    2 * number E + M.edgeFinset.card + 2 ≤ 2 * number G := by
  have hRG : E \ M ≤ G := sdiff_le.trans hEG
  have hRne : E \ M ≠ G := by
    intro heq
    apply hne
    apply le_antisymm hEG
    simpa only [heq] using (sdiff_le : E \ M ≤ E)
  have hl := hm _ hRG hRne
  have hb := delete_matching_number hME hE hM
  omega

end Erdos184Work.MatchingDeletion
#print axioms Erdos184Work.MatchingDeletion.delete_matching_number

#print axioms Erdos184Work.MatchingDeletion.hull_matching_boost
#print axioms Erdos184Work.MatchingDeletion.minimal_even_matching_gap
