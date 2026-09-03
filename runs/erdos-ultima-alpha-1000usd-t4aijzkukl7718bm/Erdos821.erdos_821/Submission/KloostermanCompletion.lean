import Submission.KloostermanFourthMoment

/-!
# Weighted completion for finite-field Kloosterman sums

The completion identity keeps the Fourier mass of the weight explicit.
In particular no smooth-prime pool is assumed to have small Fourier mass.
-/
open Finset
open scoped Classical BigOperators ComplexConjugate
namespace Erdos821.Kloosterman

variable {F : Type*} [Field F] [Fintype F]

lemma kloosterman_swap (ψ : AddChar F ℂ) (a b : F) :
    kloosterman ψ a b = kloosterman ψ b a := by
  unfold kloosterman
  apply Fintype.sum_equiv (Equiv.inv Fˣ)
  intro u
  simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val, inv_inv, add_comm]

theorem kloosterman_norm_fourth_le_of_ne_zero (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a b : F) (h : a ≠ 0 ∨ b ≠ 0) :
    ‖kloosterman ψ a b‖^4 ≤ 3*(Fintype.card F : ℝ)^3 := by
  rcases h with ha | hb
  · exact kloosterman_norm_fourth_le ψ hψ a b ha
  · rw [kloosterman_swap]
    exact kloosterman_norm_fourth_le ψ hψ b a hb

noncomputable def elementaryBound (F : Type*) [Fintype F] : ℝ :=
  Real.sqrt (Real.sqrt (3*(Fintype.card F : ℝ)^3))

omit [Field F] in
lemma elementaryBound_nonneg : 0 ≤ elementaryBound F := Real.sqrt_nonneg _

lemma elementaryBound_fourth : elementaryBound F ^ 4 = 3*(Fintype.card F : ℝ)^3 := by
  rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, elementaryBound,
    Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]

lemma kloosterman_norm_le (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (a b : F)
    (h : a ≠ 0 ∨ b ≠ 0) : ‖kloosterman ψ a b‖ ≤ elementaryBound F := by
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) elementaryBound_nonneg (by decide : 4 ≠ 0)).mp
  rw [elementaryBound_fourth]
  exact kloosterman_norm_fourth_le_of_ne_zero ψ hψ a b h

noncomputable def fieldFourier (ψ : AddChar F ℂ) (w : F → ℂ) (t : F) : ℂ :=
  ∑ x : F, w x * ψ (-t*x)

noncomputable def fourierMass (ψ : AddChar F ℂ) (w : F → ℂ) : ℝ :=
  ∑ t : F, ‖fieldFourier ψ w t‖

lemma fourierMass_nonneg (ψ : AddChar F ℂ) (w : F → ℂ) :
    0 ≤ fourierMass ψ w := sum_nonneg fun _ _ => norm_nonneg _

lemma fieldFourier_inversion (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (w : F → ℂ) (x : F) :
    (∑ t : F, fieldFourier ψ w t * ψ (t*x)) =
      (Fintype.card F : ℂ)*w x := by
  have hkernel (y : F) : (∑ t : F, ψ (t*(x-y))) =
      if y=x then (Fintype.card F : ℂ) else 0 := by
    rw [AddChar.sum_mulShift _ hψ]
    by_cases h : y=x
    · simp [h]
    · simp [sub_ne_zero.mpr (Ne.symm h), h]
  calc
    _ = ∑ t : F, ∑ y : F, w y*ψ (t*(x-y)) := by
      simp only [fieldFourier, sum_mul]
      apply sum_congr rfl
      intro t _
      apply sum_congr rfl
      intro y _
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = ∑ y : F, w y * ∑ t : F, ψ (t*(x-y)) := by
      rw [sum_comm]
      simp only [mul_sum]
    _ = _ := by simp [hkernel, mul_ite, mul_comm]

noncomputable def weightedKloosterman (ψ : AddChar F ℂ) (w : F → ℂ) (a b : F) : ℂ :=
  ∑ u : Fˣ, w u * ψ (a*(u : F)+b*(u : F)⁻¹)

/-- Completion is an exact identity for every complex-valued weight. -/
theorem weightedKloosterman_completion (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (w : F → ℂ) (a b : F) :
    (Fintype.card F : ℂ)*weightedKloosterman ψ w a b =
      ∑ t : F, fieldFourier ψ w t * kloosterman ψ (a+t) b := by
  calc
    _ = ∑ u : Fˣ, (∑ t : F, fieldFourier ψ w t * ψ (t*(u : F))) *
        ψ (a*(u : F)+b*(u : F)⁻¹) := by
      simp only [fieldFourier_inversion ψ hψ, weightedKloosterman, mul_sum, mul_assoc]
    _ = ∑ u : Fˣ, ∑ t : F,
        fieldFourier ψ w t * ψ ((a+t)*(u : F)+b*(u : F)⁻¹) := by
      simp only [sum_mul]
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro t _
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = _ := by rw [sum_comm]; simp only [kloosterman, mul_sum]

/-- A pointwise complete-sum bound gives a weighted bound with the exact
Fourier mass on the right. -/
theorem weightedKloosterman_norm_le_of_complete_bound (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (w : F → ℂ) (a b : F) (B : ℝ)
    (hB : ∀ t : F, ‖kloosterman ψ (a+t) b‖ ≤ B) :
    (Fintype.card F : ℝ)*‖weightedKloosterman ψ w a b‖ ≤ B*fourierMass ψ w := by
  calc
    _ = ‖(Fintype.card F : ℂ)*weightedKloosterman ψ w a b‖ := by
      rw [norm_mul, Complex.norm_natCast]
    _ = ‖∑ t : F, fieldFourier ψ w t * kloosterman ψ (a+t) b‖ := by
      rw [weightedKloosterman_completion ψ hψ]
    _ ≤ ∑ t : F, ‖fieldFourier ψ w t * kloosterman ψ (a+t) b‖ := norm_sum_le _ _
    _ ≤ ∑ t : F, ‖fieldFourier ψ w t‖ * B := by
      apply sum_le_sum
      intro t _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB t) (norm_nonneg _)
    _ = _ := by rw [← sum_mul, fourierMass, mul_comm]

/-- The elementary three-quarter-power estimate after weighted completion.
For structured weights, a separate small-Fourier-mass estimate is needed. -/
theorem weightedKloosterman_norm_le (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (w : F → ℂ) (a b : F) (hb : b ≠ 0) :
    (Fintype.card F : ℝ)*‖weightedKloosterman ψ w a b‖ ≤
      elementaryBound F * fourierMass ψ w :=
  weightedKloosterman_norm_le_of_complete_bound ψ hψ w a b (elementaryBound F)
    (fun t => kloosterman_norm_le ψ hψ (a+t) b (Or.inr hb))

end Erdos821.Kloosterman
