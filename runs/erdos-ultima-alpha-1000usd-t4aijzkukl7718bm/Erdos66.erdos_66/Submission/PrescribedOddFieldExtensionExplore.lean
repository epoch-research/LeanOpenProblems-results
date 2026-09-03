import Submission.FreshOddExtensionExplore
import Submission.OddExtensionFlatSetExplore

/-! An arbitrary prescribed old set admits a new-plane flat finite extension,
with its old memberships and all its old representation counts unchanged.
This finite-field statement has no assertion about natural-number carries. -/
namespace Erdos66PrescribedOddFieldExtension
open Erdos66FreshCurvePrefix Erdos66FreshOddExtension Erdos66OddExtensionFlatSet
  Erdos66OriginRepair Erdos66OddExtensionCharacterFiber Erdos66FiniteField
open scoped Classical
set_option maxHeartbeats 2000000

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]

lemma planeMap_pairCount (A D : Finset (F×F)) (z : F×F) :
    pairCount (A.image (planeMap (K:=E))) (D.image (planeMap (K:=E))) (planeMap z)=
      pairCount A D z := by
  unfold pairCount
  rw [Finset.filter_image,Finset.card_image_of_injective _ planeMap_injective]
  congr 1
  apply Finset.filter_congr
  intro a ha
  have he : planeMap (K:=E) z-planeMap a=planeMap (z-a) := by
    ext <;> simp [planeMap,map_sub]
  rw [he,Finset.mem_image]
  constructor
  · rintro ⟨b,hb,he⟩
    exact planeMap_injective he ▸ hb
  · intro hz
    exact ⟨z-a,hz,rfl⟩

/-- The parameter set can be chosen after the arbitrary old set. There is
no old-cardinality or old-cap error in the new-target bound. -/
theorem exists_prescribed_extension (hd : Odd (Module.finrank F E))
    (hE : ringChar E≠2) (A : Finset (F×F)) (U : Finset F)
    (hU : ∀ u∈U, u≠0) (hUU : ∀ u∈U, ∀ v∈U, u+v≠0) (hne : U.Nonempty) :
    ∃ B : Finset (E×E),
      (∀ z : F×F, planeMap z∈B ↔ z∈A) ∧
      (∀ z : F×F, pairCount B B (planeMap z)=pairCount A A z) ∧
      (∀ z : E×E, (z.1∉(algebraMap F E).fieldRange ∨ z.2∉(algebraMap F E).fieldRange) →
        |(pairCount B B z:ℤ)-(U.card:ℤ)^2|≤(∑ w : F, |charFiber U w|)+6*(U.card:ℤ)) := by
  let k := (algebraMap F E).fieldRange
  let V := U.image (algebraMap F E)
  let A' := A.image (planeMap (K:=E))
  have hA : A'⊆oldPlane k := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    exact (mem_oldPlane k (planeMap a)).mpr ⟨⟨a.1,rfl⟩,⟨a.2,rfl⟩⟩
  have hV : ∀ u∈V, u∈k ∧ u≠0 := by
    intro u hu
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    exact ⟨⟨a,rfl⟩,(map_ne_zero (algebraMap F E)).mpr (hU a ha)⟩
  have hVV : ∀ u∈V, ∀ v∈V, u+v≠0 := by
    intro u hu v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    rw [←map_add]
    exact (map_ne_zero (algebraMap F E)).mpr (hUU a ha b hb)
  have hclosed : ∀ x : E, x^2∈k → x∈k := by
    intro x hx
    exact square_in_base_of_odd_finrank hd hx
  have hcard : V.card=U.card := Finset.card_image_of_injective _ (algebraMap F E).injective
  have hB : freshParabolas k V⊆V.biUnion (freshCurve k) := by rw [freshParabolas_eq_biUnion]
  let B := A'∪freshParabolas k V
  refine ⟨B,?_,?_,?_⟩
  · intro z
    have hz : planeMap (K:=E) z∈oldPlane k :=
      (mem_oldPlane k (planeMap z)).mpr ⟨⟨z.1,rfl⟩,⟨z.2,rfl⟩⟩
    have hs := prescribed_old_slice k A' (freshParabolas k V) hA V hB
    have he : planeMap (K:=E) z∈B ↔ planeMap (K:=E) z∈A' := by
      rw [←hs,Finset.mem_inter]
      exact (and_iff_left hz).symm
    rw [he]
    exact Finset.mem_image.trans ⟨fun ⟨a,ha,he⟩ ↦ planeMap_injective he ▸ ha,
      fun hz ↦ ⟨z,hz,rfl⟩⟩
  · intro z
    have hz : planeMap (K:=E) z∈oldPlane k :=
      (mem_oldPlane k (planeMap z)).mpr ⟨⟨z.1,rfl⟩,⟨z.2,rfl⟩⟩
    change pairCount (A'∪freshParabolas k V) (A'∪freshParabolas k V) (planeMap z)=_
    rw [prescribed_old_counts k hclosed A' hA V hV hVV _ hz]
    exact planeMap_pairCount A A z
  · intro z hz
    have hz' : z∉oldPlane k := by
      rw [mem_oldPlane]
      tauto
    have hh := replacement_flat_new_targets k hE A' hA V (fun u hu ↦ (hV u hu).2)
      hVV (hne.image _) z hz'
    rw [hcard] at hh
    have hs : (∑ w : E, |charFiber V w|)=∑ w : F, |charFiber U w| :=
      sum_abs_charFiber_map hd U
    rw [hs] at hh
    exact hh

end Erdos66PrescribedOddFieldExtension
