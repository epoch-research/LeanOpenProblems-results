import Submission.SubdividedFiveAbsorption

/-! Replace one partition member by two paths, retaining an arbitrary separate subgraph. -/
namespace Erdos583TwoReplacementTransferDevelopment
open SimpleGraph Erdos583Work Erdos583OneMemberTransferDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma replace_one_by_two_general {V : Type*} {H G : SimpleGraph V}
    (D : Finset H.Subgraph) (hD : GoodDecomposition H D)
    (K : H.Subgraph) (hKD : K ∈ D)
    (A B : G.Subgraph) (hA : IsPathSubgraph A) (hB : IsPathSubgraph B)
    (hAB : Disjoint A.edgeSet B.edgeSet)
    (hAc : Disjoint A.edgeSet (H.edgeSet \ K.edgeSet))
    (hBc : Disjoint B.edgeSet (H.edgeSet \ K.edgeSet))
    (hcover : G.edgeSet=((H.edgeSet \ K.edgeSet) ∪ A.edgeSet) ∪ B.edgeSet) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  classical
  obtain ⟨C,hp,hd,hc,hcount⟩ := erase_one_transfer D hD K hKD (by
    intro e he; rw [hcover]; exact Or.inl (Or.inl he))
  have hpAB : ∀ J ∈ ({A,B} : Finset G.Subgraph), IsPathSubgraph J := by
    intro J hJ
    rcases Finset.mem_insert.mp hJ with rfl | hJ
    · exact hA
    · simpa only [Finset.mem_singleton.mp hJ] using hB
  have hdAB : Set.PairwiseDisjoint (({A,B} : Finset G.Subgraph) : Set G.Subgraph) (fun J ↦ J.edgeSet) := by
    intro J hJ L hL hne
    simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hJ hL
    rcases hJ with rfl | rfl <;> rcases hL with rfl | rfl
    · exact (hne rfl).elim
    · exact hAB
    · exact hAB.symm
    · exact (hne rfl).elim
  obtain ⟨E,hE,hEc⟩ := CutVertexReduction.union_disjoint_partitions C {A,B} hp hpAB hd hdAB
    (by
      intro J hJ L hL
      have hsub : J.edgeSet ⊆ H.edgeSet \ K.edgeSet := by
        intro e he; rw [←hc]; exact Set.mem_iUnion₂.mpr ⟨J,hJ,he⟩
      simp only [Finset.mem_insert,Finset.mem_singleton] at hL
      rcases hL with rfl | rfl
      · exact (hAc.mono_right hsub).symm
      · exact (hBc.mono_right hsub).symm)
    (by
      rw [hc]
      simpa only [Finset.mem_insert,Finset.mem_singleton,Set.iUnion_iUnion_eq_or_left,
        Set.iUnion_iUnion_eq_left,←Set.union_assoc] using hcover.symm)
  have habc : ({A,B} : Finset G.Subgraph).card ≤ 2 := (Finset.card_insert_le A {B}).trans (by simp)
  exact ⟨E,hE,by omega⟩

lemma replace_one_by_two_keeping_separate {V : Type*} {H G : SimpleGraph V}
    (D : Finset H.Subgraph) (hD : GoodDecomposition H D)
    (K : H.Subgraph) (hKD : K ∈ D)
    (C A B : G.Subgraph) (hA : IsPathSubgraph A) (hB : IsPathSubgraph B)
    (hAB : Disjoint A.edgeSet B.edgeSet)
    (hC : Disjoint C.edgeSet (A.edgeSet ∪ B.edgeSet))
    (hrest : Disjoint (C.edgeSet ∪ (A.edgeSet ∪ B.edgeSet)) (H.edgeSet \ K.edgeSet))
    (hcover : G.edgeSet=(H.edgeSet \ K.edgeSet) ∪ (C.edgeSet ∪ (A.edgeSet ∪ B.edgeSet))) :
    ∃ E : Finset (G.deleteEdges C.edgeSet).Subgraph,
      GoodDecomposition (G.deleteEdges C.edgeSet) E ∧ E.card ≤ D.card+1 := by
  obtain ⟨a,b,P,hP,hPe⟩ := hA
  obtain ⟨c,d,Q,hQ,hQe⟩ := hB
  have htP : ∀ e ∈ P.edges, e ∈ (G.deleteEdges C.edgeSet).edgeSet := by
    intro e he
    have heA : e ∈ A.edgeSet := hPe.symm ▸ P.mem_edges_toSubgraph.mpr he
    rw [edgeSet_deleteEdges]
    exact ⟨A.edgeSet_subset heA,fun heC ↦ Set.disjoint_left.mp hC heC (Or.inl heA)⟩
  have htQ : ∀ e ∈ Q.edges, e ∈ (G.deleteEdges C.edgeSet).edgeSet := by
    intro e he
    have heB : e ∈ B.edgeSet := hQe.symm ▸ Q.mem_edges_toSubgraph.mpr he
    rw [edgeSet_deleteEdges]
    exact ⟨B.edgeSet_subset heB,fun heC ↦ Set.disjoint_left.mp hC heC (Or.inr heB)⟩
  let A' := (P.transfer (G.deleteEdges C.edgeSet) htP).toSubgraph
  let B' := (Q.transfer (G.deleteEdges C.edgeSet) htQ).toSubgraph
  have hAe : A'.edgeSet=A.edgeSet := by simp only [A',hPe,Walk.edgeSet_toSubgraph,Walk.edges_transfer]
  have hBe : B'.edgeSet=B.edgeSet := by simp only [B',hQe,Walk.edgeSet_toSubgraph,Walk.edges_transfer]
  apply replace_one_by_two_general D hD K hKD A' B'
    ⟨_,_,_,hP.transfer htP,rfl⟩ ⟨_,_,_,hQ.transfer htQ,rfl⟩
  · rwa [hAe,hBe]
  · rw [hAe]; exact (disjoint_sup_left.mp (disjoint_sup_left.mp hrest).2).1
  · rw [hBe]; exact (disjoint_sup_left.mp (disjoint_sup_left.mp hrest).2).2
  · rw [hAe,hBe,edgeSet_deleteEdges,hcover]
    ext e
    constructor
    · rintro ⟨he,hn⟩
      rcases he with he | he | he | he
      · exact Or.inl (Or.inl he)
      · exact (hn he).elim
      · exact Or.inl (Or.inr he)
      · exact Or.inr he
    · rintro ((he|he)|he)
      · exact ⟨Or.inl he,fun heC ↦ Set.disjoint_left.mp hrest (Or.inl heC) he⟩
      · exact ⟨Or.inr (Or.inr (Or.inl he)),fun heC ↦ Set.disjoint_left.mp hC heC (Or.inl he)⟩
      · exact ⟨Or.inr (Or.inr (Or.inr he)),fun heC ↦ Set.disjoint_left.mp hC heC (Or.inr he)⟩

end Erdos583TwoReplacementTransferDevelopment
