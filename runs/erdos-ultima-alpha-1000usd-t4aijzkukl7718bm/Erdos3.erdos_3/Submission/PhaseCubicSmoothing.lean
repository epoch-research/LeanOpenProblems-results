import Submission.ReducedLossQuadraticInverse
import Submission.AsymmetricFourierSmoothing

/-! Cubic self-convolution of a phase-weighted indicator. After normalization,
its Fourier l1 norm is at most one, independently of the support density. -/
namespace Erdos3PhaseCubicSmoothing
open Finset Erdos3FiniteFourier Erdos3MixedCorrelationFourier Erdos3CorrelationSifting
  Erdos3AsymmetricFourierSmoothing Erdos3SpectralGraphEnergy
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def cconv (f g : G → ℂ) (x : G) : ℂ := 𝔼 b, f b*g (x-b)
noncomputable def cubic (f : G → ℂ) (x : G) : ℂ := cconv f (mixedCorr f f) x
noncomputable def phaseMask (T : Finset G) (θ : G → ℂ) (x : G) : ℂ := if x ∈ T then θ x else 0
noncomputable def cubicSmooth (T : Finset G) (θ : G → ℂ) (x : G) : ℂ :=
  ((density T : ℂ)^2)⁻¹*cubic (phaseMask T θ) x

lemma hat_cconv (f g : G → ℂ) (χ : AddChar G ℂ) :
    hat (cconv f g) χ = hat f χ*hat g χ := by
  unfold hat cconv
  simp only [expect_mul]
  rw [expect_comm]
  calc
    _ = 𝔼 b, f b*(𝔼 x, g (x-b)*conj (χ x)) := by simp only [mul_assoc,mul_expect]
    _ = 𝔼 b, f b*(conj (χ b)*hat g χ) := by
      apply expect_congr rfl
      intro b _
      congr 1
      have hh := hat_shift g (-b) χ
      simpa only [hat,sub_eq_add_neg,AddChar.map_neg_eq_inv,AddChar.inv_apply_eq_conj] using hh
    _ = _ := by simp only [← mul_assoc,← expect_mul]; rfl

lemma hat_cubic (f : G → ℂ) (χ : AddChar G ℂ) :
    hat (cubic f) χ = hat f χ*((‖hat f χ‖^2 : ℝ) : ℂ) := by
  change hat (cconv f (mixedCorr f f)) χ = _
  rw [hat_cconv,hat_mixedCorr,Complex.mul_conj,Complex.normSq_eq_norm_sq]

lemma hat_cubicSmooth (T : Finset G) (θ : G → ℂ) (χ : AddChar G ℂ) :
    hat (cubicSmooth T θ) χ = ((density T : ℂ)^2)⁻¹*
      (hat (phaseMask T θ) χ*((‖hat (phaseMask T θ) χ‖^2 : ℝ) : ℂ)) := by
  unfold hat cubicSmooth
  simp only [mul_assoc,← mul_expect]
  exact congrArg (fun z ↦ ((density T : ℂ)^2)⁻¹*z) (hat_cubic (phaseMask T θ) χ)

lemma phaseMask_norm_le (T : Finset G) (θ : G → ℂ) (hθ : ∀ x, ‖θ x‖ ≤ 1) (x : G) :
    ‖phaseMask T θ x‖ ≤ 1 := by
  unfold phaseMask
  split_ifs
  · exact hθ x
  · norm_num

lemma phaseMask_support (T : Finset G) (θ : G → ℂ) (x : G) (hx : x ∉ T) :
    phaseMask T θ x = 0 := if_neg hx

lemma norm_hat_phaseMask_le (T : Finset G) (θ : G → ℂ)
    (hθ : ∀ x, ‖θ x‖ ≤ 1) (χ : AddChar G ℂ) : ‖hat (phaseMask T θ) χ‖ ≤ density T := by
  apply (norm_hat_le _ _).trans
  rw [← expect_indicator T]
  apply expect_le_expect
  intro x _
  by_cases hx : x ∈ T
  · simpa only [phaseMask,indicator,if_pos hx] using hθ x
  · simp only [phaseMask,indicator,if_neg hx,norm_zero,le_refl]

/-- The normalization costs sigma^-2, but the three Fourier factors recover it:
one factor is bounded by sigma and the other two have total energy <=sigma. -/
theorem cubicSmooth_hat_l1_le_one (T : Finset G) (hT : T.Nonempty) (θ : G → ℂ)
    (hθ : ∀ x, ‖θ x‖ ≤ 1) :
    (∑ χ : AddChar G ℂ, ‖hat (cubicSmooth T θ) χ‖) ≤ 1 := by
  have hσ : 0 < density T := density_pos T hT
  have henergy : (∑ χ : AddChar G ℂ, ‖hat (phaseMask T θ) χ‖^2) ≤ density T := by
    rw [parseval]
    exact energy_le_density_of_support T _ (phaseMask_norm_le T θ hθ) (phaseMask_support T θ)
  calc
    _ = ∑ χ : AddChar G ℂ, ((density T)^2)⁻¹*‖hat (phaseMask T θ) χ‖*‖hat (phaseMask T θ) χ‖^2 := by
      apply sum_congr rfl
      intro χ _
      rw [hat_cubicSmooth]
      simp only [norm_mul,norm_inv,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hσ,abs_pow,abs_norm,mul_assoc]
    _ ≤ ∑ χ : AddChar G ℂ, ((density T)^2)⁻¹*density T*‖hat (phaseMask T θ) χ‖^2 := by
      apply sum_le_sum
      intro χ _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_hat_phaseMask_le T θ hθ χ) (by positivity)) (sq_nonneg _)
    _ = ((density T)^2)⁻¹*density T*(∑ χ : AddChar G ℂ, ‖hat (phaseMask T θ) χ‖^2) := (mul_sum ..).symm
    _ ≤ ((density T)^2)⁻¹*density T*density T := mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = 1 := by field_simp

lemma cubic_mask_eq (T : Finset G) (hT : T.Nonempty) (θ : G → ℂ) (x : G) :
    cubic (phaseMask T θ) x = (density T : ℂ)^2*(𝔼 b : T, 𝔼 a : T,
      phaseMask T θ (x-(b : G)+a)*θ b*conj (θ a)) := by
  have he (b : G) : mixedCorr (phaseMask T θ) (phaseMask T θ) (x-b) =
      (density T : ℂ)*(𝔼 a : T, phaseMask T θ (x-b+a)*conj (θ a)) := by
    simpa only [phaseMask,add_comm] using mixedCorr_mask T hT (phaseMask T θ) θ (x-b)
  unfold cubic cconv
  simp_rw [he]
  calc
    _ = 𝔼 b : G, if b ∈ T then (density T : ℂ)*(𝔼 a : T,
        phaseMask T θ (x-b+a)*θ b*conj (θ a)) else 0 := by
      apply expect_congr rfl
      intro b _
      by_cases hb : b ∈ T
      · simp only [phaseMask,if_pos hb,mul_expect]
        apply expect_congr rfl
        intro a _
        ring
      · simp only [phaseMask,if_neg hb,zero_mul]
    _ = (density T : ℂ)*(𝔼 b : T, (density T : ℂ)*(𝔼 a : T,
        phaseMask T θ (x-(b : G)+a)*θ b*conj (θ a))) := complex_masked_expect T hT _
    _ = _ := by rw [← mul_expect]; ring

lemma cubicSmooth_eq (T : Finset G) (hT : T.Nonempty) (θ : G → ℂ) (x : G) :
    cubicSmooth T θ x = 𝔼 b : T, 𝔼 a : T,
      phaseMask T θ (x-(b : G)+a)*θ b*conj (θ a) := by
  have hσ : (density T : ℂ) ≠ 0 := by exact_mod_cast (density_pos T hT).ne'
  rw [cubicSmooth,cubic_mask_eq T hT,← mul_assoc,inv_mul_cancel₀ (pow_ne_zero 2 hσ),one_mul]

#print axioms cubicSmooth_hat_l1_le_one
#print axioms cubicSmooth_eq
end Erdos3PhaseCubicSmoothing
