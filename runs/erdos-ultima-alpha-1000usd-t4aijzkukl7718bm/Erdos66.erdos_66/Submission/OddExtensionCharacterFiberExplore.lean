import Submission.OddFieldExtensionExplore

/-! The old signed additive-fiber energy survives an odd-degree field
extension exactly. No integer ordering is asserted here. -/
namespace Erdos66OddExtensionCharacterFiber
open Erdos66OddFieldExtension Erdos66FiniteField
open scoped Classical
set_option maxHeartbeats 1800000

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]

lemma mapped_charFiber (hd : Odd (Module.finrank F K)) (U : Finset F) (w : F) :
    charFiber (U.image (algebraMap F K)) (algebraMap F K w)=charFiber U w := by
  simp only [charFiber,Finset.sum_image (algebraMap F K).injective.injOn,
    ←map_add,(algebraMap F K).injective.eq_iff,quadraticChar_algebraMap hd]

lemma mapped_charFiber_outside (U : Finset F) (w : K)
    (hw : w∉Set.range (algebraMap F K)) :
    charFiber (U.image (algebraMap F K)) w=0 := by
  simp only [charFiber,Finset.sum_image (algebraMap F K).injective.injOn]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  have hn : algebraMap F K u+algebraMap F K v≠w := by
    intro he
    exact hw ⟨u+v,by simpa only [map_add] using he⟩
  simp only [hn,if_false]

/-- Exact preservation, with no dependence on the extension-field size. -/
theorem sum_abs_charFiber_map (hd : Odd (Module.finrank F K)) (U : Finset F) :
    (∑ w : K, |charFiber (U.image (algebraMap F K)) w|)=∑ w : F, |charFiber U w| := by
  have hs : (∑ w∈Finset.univ.image (algebraMap F K),
      |charFiber (U.image (algebraMap F K)) w|)=
      ∑ w : K, |charFiber (U.image (algebraMap F K)) w| := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro w hw hn
    have hn' : w∉Set.range (algebraMap F K) := by simpa using hn
    rw [mapped_charFiber_outside U w hn',abs_zero]
  rw [←hs,Finset.sum_image (algebraMap F K).injective.injOn]
  simp_rw [mapped_charFiber hd]

/-- Every new field target has the same old absolute character-error budget. -/
theorem extended_graphCount_error (hd : Odd (Module.finrank F K))
    (hK : ringChar K≠2) (U : Finset F)
    (hU : ∀ u∈U, u≠0) (hUU : ∀ u∈U, ∀ v∈U, u+v≠0) (t s : K) :
    |graphCount (U.image (algebraMap F K)) t s-(U.card:ℤ)^2|≤
      ∑ w : F, |charFiber U w| := by
  have hu : ∀ u∈U.image (algebraMap F K), u≠0 := by
    intro u hu
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    exact (map_ne_zero (algebraMap F K)).mpr (hU v hv)
  have huu : ∀ u∈U.image (algebraMap F K), ∀ v∈U.image (algebraMap F K), u+v≠0 := by
    intro u hu v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    rw [←map_add]
    exact (map_ne_zero (algebraMap F K)).mpr (hUU a ha b hb)
  have hh := graphCount_error_bound hK (U.image (algebraMap F K)) hu huu t s
  rw [Finset.card_image_of_injective _ (algebraMap F K).injective,
    sum_abs_charFiber_map hd U] at hh
  exact hh

end Erdos66OddExtensionCharacterFiber
