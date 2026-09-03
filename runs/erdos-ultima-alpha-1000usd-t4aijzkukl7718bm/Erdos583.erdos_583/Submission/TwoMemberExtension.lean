import Submission.CubicTriangleEvenChord

/-! Extending two distinct members by disjoint sets of new edges. -/
namespace Erdos583TwoMemberExtensionDevelopment
open SimpleGraph Erdos583Work
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma extend_two_members {V : Type*} {H G : SimpleGraph V} (hHG : H ≤ G)
    (D : Finset H.Subgraph) (hD : GoodDecomposition H D)
    (P Q : H.Subgraph) (hP : P ∈ D) (hQ : Q ∈ D) (hPQ : P ≠ Q)
    (A B : G.Subgraph) (hA : IsPathSubgraph A) (hB : IsPathSubgraph B)
    (EA EB : Set (Sym2 V))
    (hAe : A.edgeSet=P.edgeSet ∪ EA) (hBe : B.edgeSet=Q.edgeSet ∪ EB)
    (haH : Disjoint EA H.edgeSet) (hbH : Disjoint EB H.edgeSet) (hab : Disjoint EA EB)
    (hcover : G.edgeSet=(H.edgeSet ∪ EA) ∪ EB) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card := by
  classical
  let f (K : H.Subgraph) : G.Subgraph := if K=P then A else if K=Q then B else K.map (Hom.ofLE hHG)
  have hfp : f P=A := by simp [f]
  have hfq : f Q=B := by simp [f,hPQ.symm]
  have hfo (K : H.Subgraph) (hp : K ≠ P) (hq : K ≠ Q) :
      (f K).edgeSet=K.edgeSet := by simp only [f,if_neg hp,if_neg hq,edgeSet_lift]
  have hsub (K : H.Subgraph) : K.edgeSet ⊆ (f K).edgeSet := by
    by_cases hp : K=P
    · subst K; rw [hfp,hAe]; exact Set.subset_union_left
    by_cases hq : K=Q
    · subst K; rw [hfq,hBe]; exact Set.subset_union_left
    rw [hfo K hp hq]
  have hpaths (K : H.Subgraph) (hK : K ∈ D) : IsPathSubgraph (f K) := by
    by_cases hp : K=P
    · subst K; rw [hfp]; exact hA
    by_cases hq : K=Q
    · subst K; rw [hfq]; exact hB
    simp only [f,if_neg hp,if_neg hq]
    exact lift_path_subgraph hHG (hD.1 K hK)
  have hAB : Disjoint A.edgeSet B.edgeSet := by
    rw [hAe,hBe]
    exact disjoint_sup_left.mpr ⟨disjoint_sup_right.mpr ⟨hD.2.1 hP hQ hPQ,
      (hbH.mono_right P.edgeSet_subset).symm⟩,
      disjoint_sup_right.mpr ⟨haH.mono_right Q.edgeSet_subset,hab⟩⟩
  have hAo (K : H.Subgraph) (hK : K ∈ D) (hp : K ≠ P) : Disjoint A.edgeSet K.edgeSet := by
    rw [hAe]
    exact disjoint_sup_left.mpr ⟨hD.2.1 hP hK hp.symm,haH.mono_right K.edgeSet_subset⟩
  have hBo (K : H.Subgraph) (hK : K ∈ D) (hq : K ≠ Q) : Disjoint B.edgeSet K.edgeSet := by
    rw [hBe]
    exact disjoint_sup_left.mpr ⟨hD.2.1 hQ hK hq.symm,hbH.mono_right K.edgeSet_subset⟩
  have hdis (K : H.Subgraph) (hK : K ∈ D) (J : H.Subgraph) (hJ : J ∈ D) (hKJ : K ≠ J) :
      Disjoint (f K).edgeSet (f J).edgeSet := by
    by_cases hp : K=P
    · subst K
      rw [hfp]
      by_cases hq : J=Q
      · subst J; rw [hfq]; exact hAB
      · rw [hfo J hKJ.symm hq]; exact hAo J hJ hKJ.symm
    by_cases hq : K=Q
    · subst K
      rw [hfq]
      by_cases hp' : J=P
      · subst J; rw [hfp]; exact hAB.symm
      · rw [hfo J hp' hKJ.symm]; exact hBo J hJ hKJ.symm
    rw [hfo K hp hq]
    by_cases hp' : J=P
    · subst J; rw [hfp]; exact (hAo K hK hp).symm
    by_cases hq' : J=Q
    · subst J; rw [hfq]; exact (hBo K hK hq).symm
    rw [hfo J hp' hq']
    exact hD.2.1 hK hJ hKJ
  refine ⟨D.image f,⟨?_,?_,?_⟩,Finset.card_image_le⟩
  · intro K hK
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hK
    exact hpaths J hJ
  · intro A' hA' B' hB' hne
    obtain ⟨K,hKD,hKA⟩ := Finset.mem_image.mp hA'
    obtain ⟨J,hJD,hJB⟩ := Finset.mem_image.mp hB'
    subst A' B'
    exact hdis K hKD J hJD (fun he ↦ hne (congrArg f he))
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨K,_,he⟩; exact K.edgeSet_subset he
    · intro he
      rw [hcover] at he
      rcases he with (he|he)|he
      · have hh : e ∈ ⋃ K ∈ D, K.edgeSet := hD.2.2.symm ▸ he
        simp only [Set.mem_iUnion] at hh
        obtain ⟨J,hJ,heJ⟩ := hh
        exact ⟨f J,Finset.mem_image.mpr ⟨J,hJ,rfl⟩,hsub J heJ⟩
      · exact ⟨f P,Finset.mem_image.mpr ⟨P,hP,rfl⟩,by rw [hfp,hAe]; exact Or.inr he⟩
      · exact ⟨f Q,Finset.mem_image.mpr ⟨Q,hQ,rfl⟩,by rw [hfq,hBe]; exact Or.inr he⟩

end Erdos583TwoMemberExtensionDevelopment
