import Submission.PrescribedOddFieldExtensionExplore

/-! A concrete instantiation of prescribed-old-set extension, using a
quadratic coset followed by an odd-degree extension. No natural-number
prefix assertion is made. -/
namespace Erdos66CosetPrescribedExtension
open Erdos66PrescribedOddFieldExtension Erdos66OddExtensionFlatSet
  Erdos66OriginRepair Erdos66FiniteField Erdos66Coset Erdos66CharacterNorm
open scoped Classical
set_option maxHeartbeats 1800000

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Fintype K] [DecidableEq K] [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E] [Algebra K F] [Algebra F E]

/-- A uniform new-target template can be chosen after an arbitrary old set.
Its error is O(q^(3/2)) about the mean q^2, with no old-set error term. Old
membership and all old target counts are inherited exactly. -/
theorem exists_flat_prescribed_extension (hK : ringChar K≠2)
    (hKF : Module.finrank K F=2) (hFE : Odd (Module.finrank F E))
    (A : Finset (F×F)) :
    ∃ (B : Finset (E×E)) (err : ℤ), 0≤err ∧ err^2≤3*(Fintype.card K:ℤ)^3 ∧
      (∀ z : F×F, planeMap z∈B ↔ z∈A) ∧
      (∀ z : F×F, pairCount B B (planeMap z)=pairCount A A z) ∧
      (∀ z : E×E, (z.1∉(algebraMap F E).fieldRange ∨ z.2∉(algebraMap F E).fieldRange) →
        |(pairCount B B z:ℤ)-(Fintype.card K:ℤ)^2|≤err+6*(Fintype.card K:ℤ)) := by
  have hF : ringChar F≠2 := by rw [ringChar_eq_of_algebra (K:=K)]; exact hK
  have hE : ringChar E≠2 := by rw [ringChar_eq_of_algebra (K:=F)]; exact hF
  have hcard : Fintype.card F=Fintype.card K^2 := by
    rw [Module.card_eq_pow_finrank (K:=K) (V:=F),hKF]
  obtain ⟨ν,hν⟩ := FiniteField.exists_nonsquare hK
  have hν0 : ν≠0 := fun he ↦ hν (he ▸ IsSquare.zero)
  have hsquare : IsSquare (algebraMap K F ν) := by
    apply (quadraticChar_one_iff_isSquare ((map_ne_zero (algebraMap K F)).mpr hν0)).mp
    rw [quadraticChar_norm hK hF,Algebra.norm_algebraMap,hKF]
    exact quadraticChar_sq_one' hν0
  obtain ⟨α,hα⟩ := (isSquare_iff_exists_sq _).mp hsquare
  have hbase := root_not_in_base ν hν α hα.symm
  let U := affineCoset (K:=K) α
  have hU : ∀ u∈U, u≠0 :=
    fun u hu he ↦ affineCoset_zero_not_mem α hbase (he ▸ hu)
  have hUU : ∀ u∈U, ∀ v∈U, u+v≠0 := affineCoset_no_opposites hK α hbase
  have hchar (x : K) : quadraticChar F (α+algebraMap K F x)=quadraticChar K (x^2-ν) :=
    quadraticChar_quadratic_coset hK hF hcard ν hν α hα.symm x
  have hUcard : U.card=Fintype.card K := affineCoset_card α
  obtain ⟨B,hBslice,hBcounts,hBnew⟩ := exists_prescribed_extension hFE hE A U hU hUU
    (affineCoset_nonempty α)
  refine ⟨B,∑ w : F, |charFiber U w|,Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _),
    affineCoset_l1_sq hK α ν hν hchar,hBslice,hBcounts,?_⟩
  intro z hz
  simpa only [hUcard] using hBnew z hz

end Erdos66CosetPrescribedExtension
