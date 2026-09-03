import Submission.DegenerateCrossGraphExplore
import Submission.RectangleRepairExplore

/-! Reflection and nonzero-target difference estimates for the two-curve
origin repair. -/
namespace Erdos66SumDifferenceRepair
open Erdos66OriginRepair Erdos66FiniteField Erdos66CrossGraph
  Erdos66ParabolaRepair Erdos66AsymmetricRepair
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma parabolaSet_neg (U : Finset F) :
    (parabolaSet U).image Neg.neg = parabolaSet (U.image Neg.neg) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨u,hu,he⟩ := (Finset.mem_filter.mp hx).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, -u, Finset.mem_image.mpr ⟨u,hu,rfl⟩,?_⟩
    dsimp
    rw [neg_sq,div_neg,he]
  · intro hz
    obtain ⟨v,hv,he⟩ := (Finset.mem_filter.mp hz).2
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨-z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,hu,?_⟩,neg_neg z⟩
    dsimp
    rw [neg_sq,he,div_neg,neg_neg]

lemma parabolaSet_pm_neg (w : F) :
    (parabolaSet ({w,-w} : Finset F)).image Neg.neg = parabolaSet {w,-w} := by
  rw [parabolaSet_neg]
  congr 1
  ext x
  simp only [Finset.mem_image,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨y,(rfl | rfl),rfl⟩ <;> simp
  · intro hx
    rcases hx with hx | hx
    · exact ⟨-w,Or.inr rfl,(neg_neg w).trans hx.symm⟩
    · exact ⟨w,Or.inl rfl,hx.symm⟩

lemma reflected_repair_bounds (hF : ringChar F ≠ 2) (U V : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hV : ∀ v ∈ V, v ≠ 0)
    (w : F) (hw : w ≠ 0) (D E : Finset (F × F))
    (hD : D ⊆ parabolaSet {w,-w}) (hE : E ⊆ parabolaSet {w,-w})
    (hUD : Disjoint (parabolaSet U) D) (hVE : Disjoint (parabolaSet V) E)
    (z : F × F) (hz : z ≠ 0) :
    pairCount (parabolaSet U) ((parabolaSet V).image Neg.neg) z ≤
      pairCount (parabolaSet U ∪ D) ((parabolaSet V ∪ E).image Neg.neg) z ∧
    pairCount (parabolaSet U ∪ D) ((parabolaSet V ∪ E).image Neg.neg) z ≤
      pairCount (parabolaSet U) ((parabolaSet V).image Neg.neg) z +
        4*U.card+4*V.card+8 := by
  have hEn : E.image Neg.neg ⊆ parabolaSet {w,-w} := by
    have hh := Finset.image_subset_image (f := Neg.neg) hE
    rwa [parabolaSet_pm_neg] at hh
  have hVn : ∀ v ∈ V.image Neg.neg, v ≠ 0 := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    exact neg_ne_zero.mpr (hV u hu)
  have hpm : ∀ v ∈ ({w,-w} : Finset F), v ≠ 0 := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hw
    · rw [Finset.mem_singleton.mp hv]
      exact neg_ne_zero.mpr hw
  have hc : ({w,-w} : Finset F).card = 2 := by simp [parameter_ne_neg hF hw]
  have h₁ := (pairCount_mono (Finset.Subset.refl (parabolaSet U)) hEn z).trans
    (parabolaSet_pairCount_le hF U {w,-w} hU hpm z hz)
  have h₂ : pairCount D ((parabolaSet V).image Neg.neg) z ≤ 4*V.card := by
    rw [parabolaSet_neg]
    have hh := (pairCount_mono hD (Finset.Subset.refl _) z).trans
      (parabolaSet_pairCount_le hF {w,-w} (V.image Neg.neg) hpm hVn z hz)
    rw [hc,Finset.card_image_of_injective _ neg_injective] at hh
    omega
  have h₃ := (pairCount_mono hD hEn z).trans
    (parabolaSet_pairCount_le hF {w,-w} {w,-w} hpm hpm z hz)
  rw [hc] at h₁ h₃
  rw [Finset.image_union,pairCount_union_mixed _ _ _ _ _ hUD
    ((Finset.disjoint_image neg_injective).mpr hVE)]
  constructor <;> omega

end Erdos66SumDifferenceRepair
