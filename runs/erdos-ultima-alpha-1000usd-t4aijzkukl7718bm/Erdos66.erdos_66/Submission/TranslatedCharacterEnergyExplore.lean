import Submission.CharacterEnergyExplore
import Submission.CyclicVarianceExplore

/-! Averaged additive energy of a quadratic character restricted to translates
of an arbitrary finite set. No prescribed Legendre-symbol pattern or special
choice of prime is required for this average estimate. -/
namespace Erdos66TranslatedCharacterEnergy
open Erdos66CharacterEnergy
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma shiftSum_energy_le_card {ι : Type*} (hF : ringChar F ≠ 2)
    (S : Finset ι) (b : ι → F)
    (hfiber : ∀ i ∈ S, (S.filter (fun j ↦ b i=b j)).card ≤ 2) :
    (∑ x : F, (shiftSum S b x)^2) ≤ 2*(Fintype.card F : ℤ)*S.card := by
  have hf (i : ι) (hi : i ∈ S) :
      (∑ j ∈ S, if b i=b j then (1 : ℤ) else 0) ≤ 2 := by
    have he : (∑ j ∈ S, if b i=b j then (1 : ℤ) else 0) =
        ((S.filter (fun j ↦ b i=b j)).card : ℤ) := by
      simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [he]
    exact_mod_cast hfiber i hi
  have hb : (∑ i ∈ S, ∑ j ∈ S, if b i=b j then (1 : ℤ) else 0) ≤ 2*S.card := by
    calc
      _ ≤ ∑ _i ∈ S, (2 : ℤ) := Finset.sum_le_sum hf
      _ = _ := by simp [mul_comm]
  rw [shiftSum_energy_identity hF]
  have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (Fintype.card F))
  nlinarith [sq_nonneg (S.card : ℤ)]

noncomputable def sumFiber (U : Finset F) (z : F) : Finset F :=
  U.filter (fun x ↦ z-x ∈ U)

noncomputable def translatedFiber (U : Finset F) (a z : F) : ℤ :=
  ∑ x ∈ sumFiber U z, quadraticChar F (a+x)*quadraticChar F (a+(z-x))

noncomputable def translatedEnergy (U : Finset F) (a : F) : ℤ :=
  ∑ z : F, (translatedFiber U a z)^2

lemma character_product_square (hF : ringChar F ≠ 2) (a z x : F) :
    quadraticChar F (a+x)*quadraticChar F (a+(z-x)) =
      quadraticChar F ((a+z/2)^2-(x-z/2)^2) := by
  rw [← map_mul]
  congr 1
  field_simp [Ring.two_ne_zero hF]
  ring

lemma translatedFiber_as_shiftSum (hF : ringChar F ≠ 2) (U : Finset F) (a z : F) :
    translatedFiber U a z =
      shiftSum (sumFiber U z) (fun x ↦ (x-z/2)^2) ((a+z/2)^2) := by
  unfold translatedFiber shiftSum
  apply Finset.sum_congr rfl
  intro x hx
  exact character_product_square hF a z x

omit [Fintype F] in
lemma symmetric_square_fiber_le_two (hF : ringChar F ≠ 2) (S : Finset F) (z x : F) :
    (S.filter (fun y ↦ (x-z/2)^2=(y-z/2)^2)).card ≤ 2 := by
  apply le_trans (Finset.card_le_card (t := {x,z-x}) ?_) Finset.card_le_two
  intro y hy
  have he := (Finset.mem_filter.mp hy).2
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
  · apply Finset.mem_insert.mpr
    left
    linear_combination -he
  · apply Finset.mem_insert.mpr
    right
    apply Finset.mem_singleton.mpr
    have hz : z/2+z/2=z := by
      field_simp [Ring.two_ne_zero hF]
      ring
    linear_combination he + hz

/-- For each additive fiber, averaging over the parameter translation costs
at most four times the field size times the number of pairs in that fiber. -/
lemma average_fiber_energy (hF : ringChar F ≠ 2) (U : Finset F) (z : F) :
    (∑ a : F, (translatedFiber U a z)^2) ≤
      4*(Fintype.card F : ℤ)*(sumFiber U z).card := by
  simp_rw [translatedFiber_as_shiftSum hF]
  have he := Equiv.sum_comp (Equiv.addRight (z/2))
    (fun a : F ↦ (shiftSum (sumFiber U z) (fun x ↦ (x-z/2)^2) (a^2))^2)
  simp only [Equiv.coe_addRight] at he
  rw [he]
  have h₁ := sum_sq_comp_square_le_two (shiftSum (sumFiber U z) (fun x ↦ (x-z/2)^2))
  have h₂ := shiftSum_energy_le_card hF (sumFiber U z) (fun x ↦ (x-z/2)^2)
    (fun x hx ↦ symmetric_square_fiber_le_two hF (sumFiber U z) z x)
  nlinarith

lemma sumFiber_mass (U : Finset F) :
    (∑ z : F, ((sumFiber U z).card : ℤ)) = (U.card : ℤ)^2 := by
  have hh := Erdos66CyclicVariance.sum_conv
    (Erdos66CyclicVariance.indicator U) (Erdos66CyclicVariance.indicator U)
  simp only [Erdos66CyclicVariance.conv_indicator,Erdos66CyclicVariance.sum_indicator] at hh
  have he : (∑ z : F, ((sumFiber U z).card : ℝ)) = (U.card : ℝ)^2 := by
    convert hh using 1
    · apply Finset.sum_congr rfl
      intro z hz
      congr 2
      ext x
      simp [sumFiber]
    · ring
  exact_mod_cast he

/-- An elementary averaged fourth-energy estimate. It applies in every finite
field of odd characteristic and to every finite set of parameters. -/
theorem average_translated_energy (hF : ringChar F ≠ 2) (U : Finset F) :
    (∑ a : F, translatedEnergy U a) ≤ 4*(Fintype.card F : ℤ)*(U.card : ℤ)^2 := by
  unfold translatedEnergy
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ z : F, 4*(Fintype.card F : ℤ)*(sumFiber U z).card :=
      Finset.sum_le_sum (fun z _ ↦ average_fiber_energy hF U z)
    _ = _ := by rw [← Finset.mul_sum,sumFiber_mass]

/-- At least one translation has the small energy, with a constant independent
of the field size. -/
theorem exists_small_energy_translate (hF : ringChar F ≠ 2) (U : Finset F) :
    ∃ a : F, translatedEnergy U a ≤ 4*(U.card : ℤ)^2 := by
  obtain ⟨a,ha,hmin⟩ := Finset.exists_min_image Finset.univ (translatedEnergy U)
    (Finset.univ_nonempty : (Finset.univ : Finset F).Nonempty)
  refine ⟨a,?_⟩
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun x hx ↦ hmin x hx)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hl
  have hu := average_translated_energy hF U
  have hp : (0 : ℤ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  nlinarith

end Erdos66TranslatedCharacterEnergy
