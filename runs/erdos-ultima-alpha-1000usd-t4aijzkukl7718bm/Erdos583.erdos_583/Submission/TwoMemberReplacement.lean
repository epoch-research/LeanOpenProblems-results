import Submission.ButterflyTwoPaths

/-! Replacing two partition members by two paths at no increase in cardinality. -/
namespace Erdos583TwoMemberReplacementDevelopment
open SimpleGraph Erdos583Work
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma replace_two_by_two {V : Type*} {H G : SimpleGraph V} (hHG : H ≤ G)
    (D : Finset H.Subgraph) (hD : GoodDecomposition H D)
    (K L : H.Subgraph) (hK : K ∈ D) (hL : L ∈ D) (hKL : K ≠ L)
    (A B : G.Subgraph) (hA : IsPathSubgraph A) (hB : IsPathSubgraph B)
    (hAB : Disjoint A.edgeSet B.edgeSet)
    (hrest : Disjoint (A.edgeSet ∪ B.edgeSet) (H.edgeSet \ (K.edgeSet ∪ L.edgeSet)))
    (hcover : G.edgeSet=(H.edgeSet \ (K.edgeSet ∪ L.edgeSet)) ∪ (A.edgeSet ∪ B.edgeSet)) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card := by
  classical
  let f (J : H.Subgraph) : G.Subgraph := if J=K then A else if J=L then B else J.map (Hom.ofLE hHG)
  have hfk : f K=A := by simp [f]
  have hfl : f L=B := by simp [f,hKL.symm]
  have hfo (J : H.Subgraph) (hk : J ≠ K) (hl : J ≠ L) : (f J).edgeSet=J.edgeSet := by
    simp only [f,if_neg hk,if_neg hl,edgeSet_lift]
  have hsub (J : H.Subgraph) (hJ : J ∈ D) (hk : J ≠ K) (hl : J ≠ L) :
      J.edgeSet ⊆ H.edgeSet \ (K.edgeSet ∪ L.edgeSet) := by
    intro e he
    refine ⟨J.edgeSet_subset he,?_⟩
    rintro (heK|heL)
    · exact Set.disjoint_left.mp (hD.2.1 hJ hK hk) he heK
    · exact Set.disjoint_left.mp (hD.2.1 hJ hL hl) he heL
  have hAo (J : H.Subgraph) (hJ : J ∈ D) (hk : J ≠ K) (hl : J ≠ L) :
      Disjoint A.edgeSet J.edgeSet := (disjoint_sup_left.mp hrest).1.mono_right (hsub J hJ hk hl)
  have hBo (J : H.Subgraph) (hJ : J ∈ D) (hk : J ≠ K) (hl : J ≠ L) :
      Disjoint B.edgeSet J.edgeSet := (disjoint_sup_left.mp hrest).2.mono_right (hsub J hJ hk hl)
  have hp (J : H.Subgraph) (hJ : J ∈ D) : IsPathSubgraph (f J) := by
    by_cases hk : J=K
    · subst J; rwa [hfk]
    by_cases hl : J=L
    · subst J; rwa [hfl]
    simp only [f,if_neg hk,if_neg hl]
    exact lift_path_subgraph hHG (hD.1 J hJ)
  have hd (J : H.Subgraph) (hJ : J ∈ D) (M : H.Subgraph) (hM : M ∈ D) (hne : J ≠ M) :
      Disjoint (f J).edgeSet (f M).edgeSet := by
    by_cases hjk : J=K
    · subst J
      rw [hfk]
      by_cases hml : M=L
      · subst M; rwa [hfl]
      rw [hfo M hne.symm hml]
      exact hAo M hM hne.symm hml
    by_cases hjl : J=L
    · subst J
      rw [hfl]
      by_cases hmk : M=K
      · subst M; rw [hfk]; exact hAB.symm
      rw [hfo M hmk hne.symm]
      exact hBo M hM hmk hne.symm
    rw [hfo J hjk hjl]
    by_cases hmk : M=K
    · subst M; rw [hfk]; exact (hAo J hJ hjk hjl).symm
    by_cases hml : M=L
    · subst M; rw [hfl]; exact (hBo J hJ hjk hjl).symm
    rw [hfo M hmk hml]
    exact hD.2.1 hJ hM hne
  refine ⟨D.image f,⟨?_,?_,?_⟩,Finset.card_image_le⟩
  · intro J hJ
    obtain ⟨M,hM,rfl⟩ := Finset.mem_image.mp hJ
    exact hp M hM
  · intro J hJ M hM hne
    obtain ⟨J',hJ',rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨M',hM',rfl⟩ := Finset.mem_image.mp hM
    exact hd J' hJ' M' hM' (fun he ↦ hne (congrArg f he))
  · ext e
    constructor
    · intro he
      obtain ⟨J,_,heJ⟩ := Set.mem_iUnion₂.mp he
      exact J.edgeSet_subset heJ
    · intro he
      rw [hcover] at he
      rcases he with he | he | he
      · obtain ⟨J,hJ,heJ⟩ := Set.mem_iUnion₂.mp (hD.2.2.symm ▸ he.1)
        have hjk : J ≠ K := fun h ↦ he.2 (Or.inl (h ▸ heJ))
        have hjl : J ≠ L := fun h ↦ he.2 (Or.inr (h ▸ heJ))
        exact Set.mem_iUnion₂.mpr ⟨f J,Finset.mem_image.mpr ⟨J,hJ,rfl⟩,
          (hfo J hjk hjl).symm ▸ heJ⟩
      · exact Set.mem_iUnion₂.mpr ⟨f K,Finset.mem_image.mpr ⟨K,hK,rfl⟩,hfk.symm ▸ he⟩
      · exact Set.mem_iUnion₂.mpr ⟨f L,Finset.mem_image.mpr ⟨L,hL,rfl⟩,hfl.symm ▸ he⟩

end Erdos583TwoMemberReplacementDevelopment
