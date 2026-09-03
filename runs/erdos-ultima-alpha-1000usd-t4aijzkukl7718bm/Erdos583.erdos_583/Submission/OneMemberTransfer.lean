import Submission.OneMemberReplacement

/-! Transferring all unselected paths between graphs that need not be comparable. -/
namespace Erdos583OneMemberTransferDevelopment
open SimpleGraph Erdos583Work
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma erase_one_transfer {V : Type*} {H G : SimpleGraph V}
    (D : Finset H.Subgraph) (hD : GoodDecomposition H D)
    (K : H.Subgraph) (hKD : K ∈ D)
    (hsub : H.edgeSet \ K.edgeSet ⊆ G.edgeSet) :
    ∃ E : Finset G.Subgraph,
      (∀ L ∈ E, IsPathSubgraph L) ∧
      Set.PairwiseDisjoint (E : Set G.Subgraph) (fun L ↦ L.edgeSet) ∧
      (⋃ L ∈ E, L.edgeSet)=H.edgeSet \ K.edgeSet ∧ E.card+1 ≤ D.card := by
  classical
  have hdata : ∀ L : {L // L ∈ D.erase K},
      ∃ A : G.Subgraph, IsPathSubgraph A ∧ A.edgeSet=L.val.edgeSet := by
    intro L
    obtain ⟨a,b,P,hP,hL⟩ := hD.1 L.val (Finset.mem_of_mem_erase L.property)
    have ht : ∀ e ∈ P.edges, e ∈ G.edgeSet := by
      intro e he
      have heL : e ∈ L.val.edgeSet := hL.symm ▸ P.mem_edges_toSubgraph.mpr he
      apply hsub
      exact ⟨L.val.edgeSet_subset heL, fun heK ↦ Set.disjoint_left.mp
        (hD.2.1 (Finset.mem_of_mem_erase L.property) hKD
          (Finset.mem_erase.mp L.property).1) heL heK⟩
    refine ⟨(P.transfer G ht).toSubgraph,⟨a,b,_,hP.transfer ht,rfl⟩,?_⟩
    simp only [hL,Walk.edgeSet_toSubgraph,Walk.edges_transfer]
  choose f hfp hfe using hdata
  let E := (D.erase K).attach.image f
  have hp : ∀ L ∈ E, IsPathSubgraph L := by
    intro L hL
    obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp hL
    exact hfp A
  have hd : Set.PairwiseDisjoint (E : Set G.Subgraph) (fun L ↦ L.edgeSet) := by
    intro A hA B hB hne
    obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨M,_,rfl⟩ := Finset.mem_image.mp hB
    change Disjoint (f L).edgeSet (f M).edgeSet
    rw [hfe,hfe]
    exact hD.2.1 (Finset.mem_of_mem_erase L.property) (Finset.mem_of_mem_erase M.property)
      (fun he ↦ hne (congrArg f (Subtype.ext he)))
  have hc : (⋃ L ∈ E, L.edgeSet)=H.edgeSet \ K.edgeSet := by
    ext e
    constructor
    · intro he
      obtain ⟨A,hA,heA⟩ := Set.mem_iUnion₂.mp he
      obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hA
      rw [hfe] at heA
      exact ⟨L.val.edgeSet_subset heA,fun heK ↦ Set.disjoint_left.mp
        (hD.2.1 (Finset.mem_of_mem_erase L.property) hKD
          (Finset.mem_erase.mp L.property).1) heA heK⟩
    · rintro ⟨he,hn⟩
      obtain ⟨L,hLD,heL⟩ := Set.mem_iUnion₂.mp (hD.2.2.symm ▸ he)
      have hLK : L ≠ K := fun hh ↦ hn (hh ▸ heL)
      let l : {L // L ∈ D.erase K} := ⟨L,Finset.mem_erase.mpr ⟨hLK,hLD⟩⟩
      exact Set.mem_iUnion₂.mpr ⟨f l,Finset.mem_image.mpr ⟨l,Finset.mem_attach _ _,rfl⟩,
        (hfe l).symm ▸ heL⟩
  have hec : E.card ≤ (D.erase K).card := by
    exact Finset.card_image_le.trans (le_of_eq Finset.card_attach)
  have hkc := Finset.card_erase_add_one hKD
  exact ⟨E,hp,hd,hc,by omega⟩

lemma replace_one_by_one {V : Type*} {H G : SimpleGraph V}
    (D : Finset H.Subgraph) (hD : GoodDecomposition H D)
    (K : H.Subgraph) (hKD : K ∈ D)
    (A : G.Subgraph) (hA : IsPathSubgraph A)
    (hdis : Disjoint A.edgeSet (H.edgeSet \ K.edgeSet))
    (hcover : G.edgeSet=(H.edgeSet \ K.edgeSet) ∪ A.edgeSet) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card := by
  classical
  have hsub : H.edgeSet \ K.edgeSet ⊆ G.edgeSet := by
    rw [hcover]; exact Set.subset_union_left
  obtain ⟨C,hp,hd,hc,hcount⟩ := erase_one_transfer D hD K hKD hsub
  obtain ⟨E,hE,hEc⟩ := CutVertexReduction.union_disjoint_partitions C {A} hp
    (by intro L hL; simpa only [Finset.mem_singleton.mp hL] using hA) hd
    (by simp)
    (by
      intro L hL M hM
      have hma : M=A := Finset.mem_singleton.mp hM
      subst M
      apply Disjoint.symm
      apply hdis.mono_right
      intro e he
      rw [←hc]
      exact Set.mem_iUnion₂.mpr ⟨L,hL,he⟩)
    (by simpa only [hc,Finset.mem_singleton,Set.iUnion_iUnion_eq_left] using hcover.symm)
  refine ⟨E,hE,?_⟩
  simp only [Finset.card_singleton] at hEc
  omega

lemma replace_one_keeping_separate {V : Type*} {H G : SimpleGraph V}
    (D : Finset H.Subgraph) (hD : GoodDecomposition H D)
    (K : H.Subgraph) (hKD : K ∈ D)
    (C Q : G.Subgraph) (hQ : IsPathSubgraph Q)
    (hdis : Disjoint C.edgeSet Q.edgeSet)
    (hrest : Disjoint (C.edgeSet ∪ Q.edgeSet) (H.edgeSet \ K.edgeSet))
    (hcover : G.edgeSet=(H.edgeSet \ K.edgeSet) ∪ (C.edgeSet ∪ Q.edgeSet)) :
    ∃ E : Finset (G.deleteEdges C.edgeSet).Subgraph,
      GoodDecomposition (G.deleteEdges C.edgeSet) E ∧ E.card ≤ D.card := by
  obtain ⟨a,b,P,hP,hQe⟩ := hQ
  have ht : ∀ e ∈ P.edges, e ∈ (G.deleteEdges C.edgeSet).edgeSet := by
    intro e he
    have heQ : e ∈ Q.edgeSet := hQe.symm ▸ P.mem_edges_toSubgraph.mpr he
    rw [edgeSet_deleteEdges]
    exact ⟨Q.edgeSet_subset heQ,fun heC ↦ Set.disjoint_left.mp hdis heC heQ⟩
  let A := (P.transfer (G.deleteEdges C.edgeSet) ht).toSubgraph
  have hAe : A.edgeSet=Q.edgeSet := by
    simp only [A,hQe,Walk.edgeSet_toSubgraph,Walk.edges_transfer]
  apply replace_one_by_one D hD K hKD A ⟨_,_,_,hP.transfer ht,rfl⟩
  · rw [hAe]
    exact (disjoint_sup_left.mp hrest).2
  · rw [hAe,edgeSet_deleteEdges,hcover]
    ext e
    constructor
    · rintro ⟨he,hn⟩
      rcases he with he | he | he
      · exact Or.inl he
      · exact (hn he).elim
      · exact Or.inr he
    · rintro (he|he)
      · exact ⟨Or.inl he,fun heC ↦ Set.disjoint_left.mp hrest (Or.inl heC) he⟩
      · exact ⟨Or.inr (Or.inr he),fun heC ↦ Set.disjoint_left.mp hdis heC he⟩

end Erdos583OneMemberTransferDevelopment
