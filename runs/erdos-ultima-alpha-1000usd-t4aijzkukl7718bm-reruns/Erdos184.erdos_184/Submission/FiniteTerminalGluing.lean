import Submission.PathUnionRank

/-! Cancellation of one shared edge across a finite vertex separator. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.FiniteTerminalGluing
open TwoTerminalGluing
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Cancel a common edge of two cycle pieces whose supports meet in at most
a finite set S. The replacement uses at most |S|-1 cycles. -/
lemma glue_cycle_pieces {A B : SimpleGraph V}
    (H : A.Subgraph) (K : B.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) {a b : V} (S : Set V)
    (habH : H.Adj a b) (habK : K.Adj a b)
    (hinter : H.verts ∩ K.verts ⊆ S)
    (hedge : H.edgeSet ∩ K.edgeSet ⊆ {s(a,b)})
    (hG : (H.edgeSet ∪ K.edgeSet) \ {s(a,b)} ⊆ G.edgeSet) :
    ∃ D : Finset G.Subgraph,
      (∀ J ∈ D, J.coe.Connected ∧ J.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun J => J.edgeSet) ∧
      (⋃ J ∈ D, J.edgeSet) = (H.edgeSet ∪ K.edgeSet) \ {s(a,b)} ∧ D.card + 1 ≤ S.ncard := by
  obtain ⟨p,hp,hpe,hpv⟩ := cycle_complementary_path H hH.1 hH.2 habH
  obtain ⟨q,hq,hqe,hqv⟩ := cycle_complementary_path K hK.1 hK.2 habK
  have hpG : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
    intro e he
    have hh := (hpe e).mp he
    exact hG ⟨Or.inl hh.1,hh.2⟩
  have hqG : ∀ e ∈ q.edges, e ∈ G.edgeSet := by
    intro e he
    have hh := (hqe e).mp he
    exact hG ⟨Or.inr hh.1,hh.2⟩
  let p' := p.transfer G hpG
  let q' := (q.transfer G hqG).reverse
  have hpp : p'.IsPath := hp.transfer hpG
  have hqq : q'.IsPath := (hq.transfer hqG).reverse
  have hd : p'.edges.Disjoint q'.edges := by
    simp only [p',q',Walk.edges_reverse,Walk.edges_transfer,List.disjoint_reverse_right]
    intro e he hf
    have ha := (hpe e).mp he
    have hb := (hqe e).mp hf
    exact ha.2 (hedge ⟨ha.1,hb.1⟩)
  have hi : p'.toSubgraph.verts ∩ q'.toSubgraph.verts ⊆ S := by
    intro x hx
    have hx' : x ∈ H.verts := hpv x (by simpa [p'] using hx.1)
    have hy' : x ∈ K.verts := hqv x (by simpa [q'] using hx.2)
    exact hinter ⟨hx',hy'⟩
  obtain ⟨D,hcD,hdD,hcov,hcard⟩ := PathUnionRank.paths_to_packing_of_inter_subset
    p' q' hpp hqq hd S hi
  refine ⟨D,hcD,hdD,?_,hcard⟩
  ext e
  rw [hcov]
  simp only [p',q',Walk.edges_transfer,Walk.edges_reverse,List.mem_reverse,hpe,hqe,
    Set.mem_diff,Set.mem_union,Set.mem_singleton_iff]
  tauto

set_option maxHeartbeats 800000 in
/-- Cancel a common artificial edge at cost at most |S|-3 beyond the total
size of the input decompositions. Supports can meet in any finite set S. -/
lemma glue_decompositions {G A B : SimpleGraph V} {a b : V} (S : Set V)
    (ha : A.Adj a b) (hb : B.Adj a b)
    (hinter : A.support ∩ B.support ⊆ S)
    (hedge : A.edgeSet ∩ B.edgeSet ⊆ {s(a,b)})
    (hcover : G.edgeSet = (A.edgeSet ∪ B.edgeSet) \ {s(a,b)})
    (DA : Finset A.Subgraph) (DB : Finset B.Subgraph)
    (hca : ∀ H ∈ DA, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hcb : ∀ H ∈ DB, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hda : IsDecomposition A DA) (hdb : IsDecomposition B DB) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card + 3 ≤ DA.card + DB.card + S.ncard := by
  have hea : s(a,b) ∈ A.edgeSet := ha
  have heb : s(a,b) ∈ B.edgeSet := hb
  rw [← hda.2] at hea
  rw [← hdb.2] at heb
  obtain ⟨H,hHD,heH⟩ := Set.mem_iUnion₂.mp hea
  obtain ⟨K,hKD,heK⟩ := Set.mem_iUnion₂.mp heb
  have hv : H.verts ∩ K.verts ⊆ S := by
    intro x hx
    exact hinter ⟨cycle_verts_subset_support H (hca H hHD).2 hx.1,
      cycle_verts_subset_support K (hcb K hKD).2 hx.2⟩
  have he : H.edgeSet ∩ K.edgeSet ⊆ {s(a,b)} := by
    intro e hh
    exact hedge ⟨H.edgeSet_subset hh.1,K.edgeSet_subset hh.2⟩
  obtain ⟨P,hcycles,hdP,hPe,hbP⟩ := glue_cycle_pieces H K (hca H hHD) (hcb K hKD) S heH heK hv he (by
    intro e he
    rw [hcover]
    exact ⟨he.1.elim (fun h => Or.inl (H.edgeSet_subset h))
      (fun h => Or.inr (K.edgeSet_subset h)),he.2⟩)
  obtain ⟨EA,hcEA,hdEA,hbEA⟩ := erase_cycle_piece DA hca hda H hHD
  obtain ⟨EB,hcEB,hdEB,hbEB⟩ := erase_cycle_piece DB hcb hdb K hKD
  let RA := A \ H.spanningCoe
  let RB := B \ K.spanningCoe
  have hJe : (unionPieces G P).edgeSet = (H.edgeSet ∪ K.edgeSet) \ {s(a,b)} :=
    (unionPieces_edgeSet G P).trans hPe
  let R := G \ unionPieces G P
  have hRA : RA ≤ R := by
    dsimp only [R]
    intro x y hxy
    have hn : s(x,y) ≠ s(a,b) := fun heq => hxy.2 (show s(x,y) ∈ H.edgeSet from heq.symm ▸ heH)
    have hxyG : G.Adj x y := by
      change s(x,y) ∈ G.edgeSet
      rw [hcover]
      exact ⟨Or.inl hxy.1,hn⟩
    refine ⟨hxyG,?_⟩
    intro hxyJ
    have hh : s(x,y) ∈ (H.edgeSet ∪ K.edgeSet) \ {s(a,b)} := hJe ▸ (show s(x,y) ∈ (unionPieces G P).edgeSet from hxyJ)
    rcases hh.1 with hh | hh
    · exact hxy.2 hh
    · exact hn (hedge ⟨hxy.1,K.edgeSet_subset hh⟩)
  have hRB : RB ≤ R := by
    dsimp only [R]
    intro x y hxy
    have hn : s(x,y) ≠ s(a,b) := fun heq => hxy.2 (show s(x,y) ∈ K.edgeSet from heq.symm ▸ heK)
    have hxyG : G.Adj x y := by
      change s(x,y) ∈ G.edgeSet
      rw [hcover]
      exact ⟨Or.inr hxy.1,hn⟩
    refine ⟨hxyG,?_⟩
    intro hxyJ
    have hh : s(x,y) ∈ (H.edgeSet ∪ K.edgeSet) \ {s(a,b)} := hJe ▸ (show s(x,y) ∈ (unionPieces G P).edgeSet from hxyJ)
    rcases hh.1 with hh | hh
    · exact hn (hedge ⟨H.edgeSet_subset hh,hxy.1⟩)
    · exact hxy.2 hh
  have hdis : Disjoint RA.edgeSet RB.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heA heB
    simp only [RA,edgeSet_sdiff] at heA
    simp only [RB,edgeSet_sdiff] at heB
    have hh : e = s(a,b) := hedge ⟨heA.1,heB.1⟩
    exact heA.2 (hh.symm ▸ heH)
  have hcov : RA.edgeSet ∪ RB.edgeSet = R.edgeSet := by
    apply Set.Subset.antisymm
    · exact Set.union_subset (edgeSet_mono hRA) (edgeSet_mono hRB)
    · intro e heR
      simp only [R,edgeSet_sdiff] at heR
      have heG := heR.1
      rw [hcover] at heG
      have hn : e ∉ H.edgeSet ∪ K.edgeSet := by
        intro he
        apply heR.2
        rw [hJe]
        exact ⟨he,heG.2⟩
      rcases heG.1 with heA | heB
      · left
        simp only [RA,edgeSet_sdiff]
        exact ⟨heA,fun he => hn (Or.inl he)⟩
      · right
        simp only [RB,edgeSet_sdiff]
        exact ⟨heB,fun he => hn (Or.inr he)⟩
  obtain ⟨E,hcE,hdE,hbE⟩ := combine_pure_decompositions hRA hRB hdis hcov EA EB
    (by
      intro L hL
      refine ⟨(hcEA L hL).1,?_⟩
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcEA L hL).2 x)
    (by
      intro L hL
      refine ⟨(hcEB L hL).1,?_⟩
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcEB L hL).2 x)
    hdEA hdEB
  obtain ⟨D,hcD,hdD,hbD⟩ := complete_cycle_packing G P hcycles hdP E (by
    intro L hL
    refine ⟨(hcE L hL).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcE L hL).2 x) hdE
  refine ⟨D,hcD,hdD,?_⟩
  omega

end Erdos184.FiniteTerminalGluing
