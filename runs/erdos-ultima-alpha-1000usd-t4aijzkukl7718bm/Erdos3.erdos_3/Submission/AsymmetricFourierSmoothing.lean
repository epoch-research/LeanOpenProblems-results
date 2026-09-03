import Submission.AsymmetricLocalization
import Submission.FourierSmoothing

/-! Fourier l1 control for asymmetric smoothing. A supported test function and one dense
outer smoothing set suffice; no inverse density of the inner smoothing set is paid. -/
namespace Erdos3AsymmetricFourierSmoothing
open Finset Erdos3FiniteFourier Erdos3FourierSmoothing Erdos3AsymmetricSifting
  Erdos3AsymmetricLocalization Erdos3CorrelationSifting Erdos3BohrLocalAverages
  Erdos3LocalCorrelationCentering Erdos3PopularAlmostPeriods Erdos3CrootSisaskL2
open scoped BigOperators Classical ComplexConjugate Pointwise
set_option maxHeartbeats 2000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def crossSmooth (S T : Finset G) (f : G → ℝ) (x : G) : ℝ :=
  𝔼 s : S, 𝔼 t : T, f (x+(t : G)-(s : G))

noncomputable def ccrossSmooth (S T : Finset G) (f : G → ℂ) (x : G) : ℂ :=
  𝔼 s : S, 𝔼 t : T, f (x+(t : G)-(s : G))

lemma crossSmooth_zero (S T : Finset G) (f : G → ℝ) :
    crossSmooth S T f 0 = crossAverage S T f := by simp only [crossSmooth, crossAverage, zero_add]

lemma crossSmooth_eq (S T : Finset G) (f : G → ℝ) (x : G) :
    smooth (-S) (smooth T f) x = crossSmooth S T f x := by
  rw [smooth_neg]
  apply expect_congr rfl
  intro s _
  apply expect_congr rfl
  intro t _
  congr 1
  abel

lemma ccrossSmooth_ofReal (S T : Finset G) (f : G → ℝ) (x : G) :
    ccrossSmooth S T (fun x ↦ (f x : ℂ)) x = (crossSmooth S T f x : ℂ) := by
  unfold ccrossSmooth crossSmooth
  rw [ofReal_expect]
  apply expect_congr rfl
  intro s _
  exact (ofReal_expect _).symm

lemma hat_ccrossSmooth (S T : Finset G) (f : G → ℂ) (χ : AddChar G ℂ) :
    hat (ccrossSmooth S T f) χ = meanChar T χ*conj (meanChar S χ)*hat f χ := by
  unfold hat ccrossSmooth
  simp_rw [expect_mul]
  calc
    _ = 𝔼 s : S, 𝔼 t : T, 𝔼 x : G,
        f (x+(t : G)-(s : G))*conj (χ x) := by
      rw [expect_comm]
      apply expect_congr rfl
      intro s _
      exact expect_comm _ _ _
    _ = 𝔼 s : S, 𝔼 t : T, χ ((t : G)-(s : G))*hat f χ := by
      apply expect_congr rfl
      intro s _
      apply expect_congr rfl
      intro t _
      simpa only [add_sub_assoc] using hat_shift f ((t : G)-(s : G)) χ
    _ = _ := by
      simp_rw [char_sub, ← expect_mul]
      rw [← mul_expect, ← expect_conj]
      rfl

/-- The squared Fourier l1 norm is bounded by the energy of f divided by density(S).
There is no density(T) term. -/
theorem ccrossSmooth_hat_l1_sq (S T : Finset G) (hS : S.Nonempty) (f : G → ℂ) :
    (∑ χ : AddChar G ℂ, ‖hat (ccrossSmooth S T f) χ‖)^2 ≤
      (𝔼 x : G, ‖f x‖^2)/density S := by
  have hpoint (χ : AddChar G ℂ) : ‖hat (ccrossSmooth S T f) χ‖ ≤
      ‖meanChar S χ‖*‖hat f χ‖ := by
    rw [hat_ccrossSmooth, norm_mul, norm_mul, Complex.norm_conj, mul_assoc]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (norm_meanChar_le_one T χ)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsum := sum_le_sum (fun χ (_ : χ ∈ (univ : Finset (AddChar G ℂ))) ↦ hpoint χ)
  calc
    _ ≤ (∑ χ : AddChar G ℂ, ‖meanChar S χ‖*‖hat f χ‖)^2 :=
      pow_le_pow_left₀ (sum_nonneg (fun _ _ ↦ norm_nonneg _)) hsum 2
    _ ≤ (∑ χ : AddChar G ℂ, ‖meanChar S χ‖^2) *
        (∑ χ : AddChar G ℂ, ‖hat f χ‖^2) := sum_mul_sq_le_sq_mul_sq ..
    _ = _ := by rw [sum_meanChar_sq S hS, parseval]; ring

lemma energy_le_density_of_support (W : Finset G) (f : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hsupport : ∀ x, x ∉ W → f x = 0) :
    (𝔼 x : G, ‖f x‖^2) ≤ density W := by
  rw [← expect_indicator W]
  apply expect_le_expect
  intro x _
  by_cases hx : x ∈ W
  · simp only [indicator, if_pos hx]
    simpa using pow_le_pow_left₀ (norm_nonneg (f x)) (hf x) 2
  · simp [indicator, hx, hsupport x hx]

/-- If f is bounded by one and supported on W, only the ratio |W|/|S| matters. -/
theorem ccrossSmooth_hat_l1_sq_support (S T W : Finset G) (hS : S.Nonempty) (f : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hsupport : ∀ x, x ∉ W → f x = 0) :
    (∑ χ : AddChar G ℂ, ‖hat (ccrossSmooth S T f) χ‖)^2 ≤ density W/density S :=
  (ccrossSmooth_hat_l1_sq S T hS f).trans
    (div_le_div_of_nonneg_right (energy_le_density_of_support W f hf hsupport) (density_nonneg S))

/-- Relative version: if S has density eta in C and W is at most K times as large
as C, the Fourier l1 norm is at most sqrt(K/eta), regardless of |T|. -/
theorem ccrossSmooth_hat_l1_sq_relative (S T C W : Finset G) (hS : S.Nonempty) (hSC : S ⊆ C)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hsupport : ∀ x, x ∉ W → f x = 0)
    {K : ℝ} (hW : density W ≤ K*density C) :
    (∑ χ : AddChar G ℂ, ‖hat (ccrossSmooth S T f) χ‖)^2 ≤ K/relativeDensity S C := by
  have hη := relativeDensity_pos S C hS hSC
  have hC := density_pos C (hS.mono hSC)
  calc
    _ ≤ density W/density S := ccrossSmooth_hat_l1_sq_support S T W hS f hf hsupport
    _ ≤ (K*density C)/density S := div_le_div_of_nonneg_right hW (density_nonneg S)
    _ = _ := by
      rw [density_eq_relative_mul S C hS hSC]
      field_simp

/-- Truncation is exact on any evaluation window whose needed cross-differences stay
in the support set. -/
lemma crossSmooth_truncate (S T W P : Finset G) (f : G → ℝ)
    (hsupport : ∀ x ∈ P, ∀ s ∈ S, ∀ t ∈ T, x+t-s ∈ W) {x : G} (hx : x ∈ P) :
    crossSmooth S T (fun y ↦ indicator W y*f y) x = crossSmooth S T f x := by
  unfold crossSmooth
  apply expect_congr rfl
  intro s _
  apply expect_congr rfl
  intro t _
  simp [indicator, hsupport x hx s s.property t t.property]

#print axioms hat_ccrossSmooth
#print axioms ccrossSmooth_hat_l1_sq_relative
#print axioms crossSmooth_truncate
end Erdos3AsymmetricFourierSmoothing
