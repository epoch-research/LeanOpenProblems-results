import Submission.Work

/-! Enlarging distinct slots of a finite path family without increasing its cardinality. -/
namespace Erdos583InjectivePathReplacementDevelopment
open SimpleGraph Erdos583Work
open scoped Classical
set_option maxHeartbeats 2000000

lemma replace_injective {V I B : Type*} [Fintype I] {G : SimpleGraph V}
    (f : I → G.Subgraph) (g : B → G.Subgraph) (slot : B → I) (hinj : Function.Injective slot)
    (hf : ∀ i, IsPathSubgraph (f i)) (hg : ∀ b, IsPathSubgraph (g b))
    (hff : Pairwise (fun i j ↦ Disjoint (f i).edgeSet (f j).edgeSet))
    (hgg : Pairwise (fun b c ↦ Disjoint (g b).edgeSet (g c).edgeSet))
    (hfg : ∀ i b, i ≠ slot b → Disjoint (f i).edgeSet (g b).edgeSet)
    (hsub : ∀ b, (f (slot b)).edgeSet ⊆ (g b).edgeSet)
    (hcover : (⋃ i, (f i).edgeSet) ∪ (⋃ b, (g b).edgeSet)=G.edgeSet) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ Fintype.card I := by
  classical
  let H (i : I) : G.Subgraph := if h : ∃ b, slot b=i then g (Classical.choose h) else f i
  have hslot (b : B) : H (slot b)=g b := by
    have hh : ∃ c, slot c=slot b := ⟨b,rfl⟩
    have he : Classical.choose hh=b := hinj (Classical.choose_spec hh)
    simp only [H,dif_pos hh,he]
  have hout (i : I) (hi : ¬∃ b, slot b=i) : H i=f i := by simp only [H,dif_neg hi]
  have hpath (i : I) : IsPathSubgraph (H i) := by
    by_cases hi : ∃ b, slot b=i
    · obtain ⟨b,rfl⟩ := hi
      rw [hslot]
      exact hg b
    · rw [hout i hi]
      exact hf i
  have hdis : Pairwise (fun i j ↦ Disjoint (H i).edgeSet (H j).edgeSet) := by
    intro i j hij
    by_cases hi : ∃ b, slot b=i
    · obtain ⟨b,rfl⟩ := hi
      rw [hslot]
      by_cases hj : ∃ c, slot c=j
      · obtain ⟨c,rfl⟩ := hj
        rw [hslot]
        exact hgg (fun he ↦ hij (congrArg slot he))
      · rw [hout j hj]
        exact (hfg j b hij.symm).symm
    · rw [hout i hi]
      by_cases hj : ∃ c, slot c=j
      · obtain ⟨c,rfl⟩ := hj
        rw [hslot]
        exact hfg i c hij
      · rw [hout j hj]
        exact hff hij
  have hc : (⋃ i, (H i).edgeSet)=G.edgeSet := by
    rw [←hcover]
    apply Set.Subset.antisymm
    · rintro e ⟨_,⟨i,rfl⟩,he⟩
      change e ∈ (H i).edgeSet at he
      by_cases hi : ∃ b, slot b=i
      · obtain ⟨b,rfl⟩ := hi
        rw [hslot] at he
        exact Or.inr (Set.mem_iUnion.mpr ⟨b,he⟩)
      · rw [hout i hi] at he
        exact Or.inl (Set.mem_iUnion.mpr ⟨i,he⟩)
    · intro e he
      rcases he with he|he
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
        by_cases hs : ∃ b, slot b=i
        · obtain ⟨b,rfl⟩ := hs
          exact Set.mem_iUnion.mpr ⟨slot b,by rw [hslot]; exact hsub b hi⟩
        · exact Set.mem_iUnion.mpr ⟨i,by rw [hout i hs]; exact hi⟩
      · obtain ⟨b,hb⟩ := Set.mem_iUnion.mp he
        exact Set.mem_iUnion.mpr ⟨slot b,by rw [hslot]; exact hb⟩
  let D := Finset.univ.image H
  refine ⟨D,⟨?_,?_,?_⟩,Finset.card_image_le.trans (by simp)⟩
  · intro K hK
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
    exact hpath i
  · intro K hK L hL hKL
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hL
    exact hdis (fun he ↦ hKL (congrArg H he))
  · simpa only [D,Finset.mem_image,Finset.mem_univ,true_and,Set.iUnion_exists,
      Set.iUnion_iUnion_eq',Set.iUnion_iUnion_eq_left] using hc

end Erdos583InjectivePathReplacementDevelopment
