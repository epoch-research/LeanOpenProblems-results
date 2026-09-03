import Submission.FiniteFourier
import Submission.PopularAlmostPeriods

/-! Fourier ℓ¹ bounds for symmetric set smoothing. Auxiliary results only. -/
namespace Erdos3FourierSmoothing
open Finset Erdos3FiniteFourier Erdos3PopularAlmostPeriods Erdos3CorrelationSifting
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 1500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma ofReal_expect {V : Type*} [Fintype V] (f : V → ℝ) :
    ((𝔼 x, f x : ℝ) : ℂ) = 𝔼 x, (f x : ℂ) :=
  map_expect ((algebraMap ℝ ℂ).toRatAlgHom.toLinearMap.restrictScalars ℚ≥0) f univ

lemma expect_mask (B : Finset G) (hB : B.Nonempty) (f : G → ℂ) :
    (𝔼 x : G, if x ∈ B then f x else 0) = (density B : ℂ)*(𝔼 b : B, f b) := by
  have hBc : (B.card : ℂ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, Fintype.card_coe]
  simp only [← sum_filter, filter_mem_eq_inter, univ_inter, sum_coe_sort, density]
  push_cast
  field_simp

noncomputable def uniform (B : Finset G) (x : G) : ℂ :=
  if x ∈ B then (density B : ℂ)⁻¹ else 0

lemma hat_uniform (B : Finset G) (hB : B.Nonempty) (χ : AddChar G ℂ) :
    hat (uniform B) χ = conj (meanChar B χ) := by
  have hα : (density B : ℂ) ≠ 0 := by exact_mod_cast (density_pos B hB).ne'
  have he (x : G) : uniform B x*conj (χ x) =
      (if x ∈ B then conj (χ x) else 0) / (density B : ℂ) := by
    by_cases hx : x ∈ B <;> simp [uniform, hx, div_eq_mul_inv, mul_comm]
  unfold hat
  simp_rw [he]
  rw [← expect_div, expect_mask B hB]
  unfold meanChar
  rw [← expect_conj]
  field_simp

lemma uniform_energy (B : Finset G) (hB : B.Nonempty) :
    (𝔼 x : G, ‖uniform B x‖^2) = 1/density B := by
  have hα := density_pos B hB
  have he (x : G) : ‖uniform B x‖^2 = indicator B x / (density B)^2 := by
    by_cases hx : x ∈ B
    · simp [uniform, indicator, hx, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hα, inv_pow]
    · simp [uniform, indicator, hx]
  simp_rw [he]
  rw [← expect_div, expect_indicator]
  field_simp [hα.ne']

lemma sum_meanChar_sq (B : Finset G) (hB : B.Nonempty) :
    (∑ χ : AddChar G ℂ, ‖meanChar B χ‖^2) = 1/density B := by
  calc
    _ = ∑ χ : AddChar G ℂ, ‖hat (uniform B) χ‖^2 := by
      simp only [hat_uniform B hB, Complex.norm_conj]
    _ = 𝔼 x : G, ‖uniform B x‖^2 := parseval _
    _ = _ := uniform_energy B hB

/-- A bounded function smoothed twice by B has Fourier ℓ¹ norm at most 1/density(B). -/
theorem cdiffSmooth_hat_l1 (B : Finset G) (hB : B.Nonempty)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    (∑ χ : AddChar G ℂ, ‖hat (cdiffSmooth B f) χ‖) ≤ 1/density B := by
  calc
    _ ≤ ∑ χ : AddChar G ℂ, ‖meanChar B χ‖^2 := by
      apply sum_le_sum
      intro χ _
      rw [hat_cdiffSmooth, norm_mul]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖meanChar B χ‖)]
      have hh : ‖hat f χ‖ ≤ 1 := (norm_hat_le f χ).trans
        (expect_le univ_nonempty (fun x _ ↦ hf x))
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (sq_nonneg ‖meanChar B χ‖)
    _ = _ := sum_meanChar_sq B hB

lemma cdiffSmooth_ofReal (B : Finset G) (f : G → ℝ) (x : G) :
    cdiffSmooth B (fun x ↦ (f x : ℂ)) x = (diffSmooth B f x : ℂ) := by
  unfold cdiffSmooth diffSmooth
  rw [ofReal_expect]
  apply expect_congr rfl
  intro b _
  exact (ofReal_expect _).symm

#print axioms sum_meanChar_sq
#print axioms cdiffSmooth_hat_l1
end Erdos3FourierSmoothing
