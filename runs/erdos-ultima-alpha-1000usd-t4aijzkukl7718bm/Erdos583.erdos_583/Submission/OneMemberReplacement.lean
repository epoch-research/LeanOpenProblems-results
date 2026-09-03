import Submission.CubicTriangleDistinctEndpoints

/-! Replacing one old member by two paths while adding edges. -/
namespace Erdos583OneMemberReplacementDevelopment
open SimpleGraph Erdos583Work
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma replace_one_by_two {V : Type*} {H G : SimpleGraph V} (hHG : H ≤ G)
    (D : Finset H.Subgraph) (hD : GoodDecomposition H D)
    (K : H.Subgraph) (hKD : K ∈ D)
    (A B : G.Subgraph) (hA : IsPathSubgraph A) (hB : IsPathSubgraph B)
    (hAB : Disjoint A.edgeSet B.edgeSet)
    (hAc : Disjoint A.edgeSet (H.edgeSet \ K.edgeSet))
    (hBc : Disjoint B.edgeSet (H.edgeSet \ K.edgeSet))
    (hcover : G.edgeSet=((H.edgeSet \ K.edgeSet) ∪ A.edgeSet) ∪ B.edgeSet) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  classical
  let C := (D.erase K).image (Subgraph.map (Hom.ofLE hHG))
  have hc : (⋃ J ∈ C, J.edgeSet)=H.edgeSet \ K.edgeSet := by
    ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨J,hJ,he⟩
      obtain ⟨L,hLD,rfl⟩ := Finset.mem_image.mp hJ
      rw [edgeSet_lift] at he
      exact ⟨L.edgeSet_subset he,fun heK ↦ Set.disjoint_left.mp
        (hD.2.1 (Finset.mem_of_mem_erase hLD) hKD (Finset.mem_erase.mp hLD).1) he heK⟩
    · rintro ⟨he,hn⟩
      have hh : e ∈ ⋃ J ∈ D, J.edgeSet := hD.2.2.symm ▸ he
      simp only [Set.mem_iUnion] at hh
      obtain ⟨J,hJD,heJ⟩ := hh
      have hJK : J ≠ K := fun h ↦ hn (h ▸ heJ)
      exact ⟨J.map (Hom.ofLE hHG),Finset.mem_image.mpr ⟨J,Finset.mem_erase.mpr ⟨hJK,hJD⟩,rfl⟩,
        (edgeSet_lift hHG J).symm ▸ heJ⟩
  have hpc : ∀ J ∈ C, IsPathSubgraph J := by
    intro J hJ
    obtain ⟨L,hLD,rfl⟩ := Finset.mem_image.mp hJ
    exact lift_path_subgraph hHG (hD.1 L (Finset.mem_of_mem_erase hLD))
  have hdc : Set.PairwiseDisjoint (C : Set G.Subgraph) (fun J ↦ J.edgeSet) := by
    intro A' hA' B' hB' hne
    obtain ⟨J,hJD,hJA⟩ := Finset.mem_image.mp hA'
    obtain ⟨L,hLD,hLB⟩ := Finset.mem_image.mp hB'
    subst A' B'
    change Disjoint (J.map (Hom.ofLE hHG)).edgeSet (L.map (Hom.ofLE hHG)).edgeSet
    rw [edgeSet_lift,edgeSet_lift]
    exact hD.2.1 (Finset.mem_of_mem_erase hJD) (Finset.mem_of_mem_erase hLD)
      (fun he ↦ hne (congrArg (Subgraph.map (Hom.ofLE hHG)) he))
  have hpAB : ∀ J ∈ ({A,B} : Finset G.Subgraph), IsPathSubgraph J := by
    intro J hJ
    simp only [Finset.mem_insert,Finset.mem_singleton] at hJ
    rcases hJ with rfl | rfl <;> assumption
  have hdAB : Set.PairwiseDisjoint (({A,B} : Finset G.Subgraph) : Set G.Subgraph) (fun J ↦ J.edgeSet) := by
    intro J hJ L hL hne
    simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hJ hL
    rcases hJ with rfl | rfl <;> rcases hL with rfl | rfl
    · exact (hne rfl).elim
    · exact hAB
    · exact hAB.symm
    · exact (hne rfl).elim
  obtain ⟨E,hE,hEc⟩ := CutVertexReduction.union_disjoint_partitions C {A,B} hpc hpAB hdc hdAB
    (by
      intro J hJ L hL
      have hsub : J.edgeSet ⊆ H.edgeSet \ K.edgeSet := by
        intro e he; rw [←hc]; exact Set.mem_iUnion.mpr ⟨J,Set.mem_iUnion.mpr ⟨hJ,he⟩⟩
      simp only [Finset.mem_insert,Finset.mem_singleton] at hL
      rcases hL with rfl | rfl
      · exact (hAc.mono_right hsub).symm
      · exact (hBc.mono_right hsub).symm)
    (by
      rw [hc,hcover]
      ext e
      simp [or_assoc])
  have hCc : C.card ≤ (D.erase K).card := Finset.card_image_le
  have hDc := Finset.card_erase_add_one hKD
  have habc : ({A,B} : Finset G.Subgraph).card ≤ 2 := (Finset.card_insert_le A {B}).trans (by simp)
  exact ⟨E,hE,by omega⟩

end Erdos583OneMemberReplacementDevelopment
