import Submission.QuadraticCircleBridge

/-! Uniformity residuals preserve the global mean, and normalized local L2
approximations preserve the average of local factor means. This supplies the
density input to a future local equidistribution/counting step. -/
namespace Erdos3LocalFactorMean
open Finset Erdos3FiniteUniformity Erdos3LinearFormsUniformity
  Erdos3QuadraticFourAPBarrier Erdos3FiniteSamplingMoments
  Erdos3StableWindowCounting
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Every Gowers uniformity norm dominates the absolute mean. The index n is
U^(n+1), raised to the power 2^(n+1). -/
theorem mean_power_le_uniformity (n : ℕ) (f : G → ℂ) :
    ‖𝔼 x : G, f x‖^(2^(n+1)) ≤ uniformityPower n f := by
  induction n generalizing f with
  | zero => exact le_rfl
  | succ n ih =>
    have hmean : ‖𝔼 x : G, f x‖^2 ≤ 𝔼 h : G, ‖𝔼 x : G, derivative f h x‖ := by
      rw [mean_complexCorr_re]
      exact expect_le_expect (fun h _ ↦ Complex.re_le_norm _)
    have heven : Even (2^(n+1)) := ⟨2^n,by rw [pow_succ]; omega⟩
    calc
      _ = (‖𝔼 x : G, f x‖^2)^(2^(n+1)) := by
        rw [← pow_mul]
        congr 1
        rw [show n+1+1 = (n+1)+1 by omega,pow_succ]
        ring
      _ ≤ (𝔼 h : G, ‖𝔼 x : G, derivative f h x‖)^(2^(n+1)) :=
        pow_le_pow_left₀ (sq_nonneg _) hmean _
      _ ≤ 𝔼 h : G, ‖𝔼 x : G, derivative f h x‖^(2^(n+1)) := expect_even_pow_le heven _
      _ ≤ uniformityPower (n+1) f := expect_le_expect (fun h _ ↦ ih (derivative f h))

lemma mean_difference_of_uniformity (n : ℕ) (f g : G → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hU : uniformityPower n (fun x ↦ ((f x-g x : ℝ) : ℂ)) ≤ η^(2^(n+1))) :
    |(𝔼 x : G, f x)-(𝔼 x : G, g x)| ≤ η := by
  have h := (mean_power_le_uniformity n (fun x ↦ ((f x-g x : ℝ) : ℂ))).trans hU
  have hnorm := le_of_pow_le_pow_left₀ (by positivity : 2^(n+1) ≠ 0) hη h
  simpa only [← Complex.ofReal_expect,Complex.norm_real,Real.norm_eq_abs,
    expect_sub_distrib] using hnorm

/-- Averaged local L2 approximation controls the averaged local mean. -/
theorem averaged_local_mean_difference (W : Finset G) (hW : W.Nonempty)
    (g : G → ℝ) (h : G → G → ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (herr : ∀ a, (𝔼 t : W, (g (a+t)-h a t)^2) ≤ κ^2) :
    |(𝔼 x : G, g x)-(𝔼 a : G, 𝔼 t : W, h a t)| ≤ κ := by
  letI : Nonempty W := hW.to_subtype
  have hmean : (𝔼 a : G, 𝔼 t : W, g (a+t)) = 𝔼 x : G, g x := by
    rw [expect_comm]
    have he (t : W) : (𝔼 a : G, g (a+t)) = 𝔼 x : G, g x :=
      Fintype.expect_equiv (Equiv.addRight (t : G)) _ _ (fun _ ↦ rfl)
    simp only [he,Fintype.expect_const]
  rw [← hmean,← expect_sub_distrib]
  apply (Finset.abs_expect_le _ _).trans
  apply expect_le univ_nonempty
  intro a _
  rw [← expect_sub_distrib]
  exact (Finset.abs_expect_le _ _).trans (mean_abs_le_of_mean_square _ hκ (herr a))

/-- The original density survives both approximation steps. No polynomiality
or distribution hypothesis is needed for this mean estimate. -/
theorem local_factor_mean_lower (n : ℕ) (W : Finset G) (hW : W.Nonempty)
    (f g : G → ℝ) (h : G → G → ℝ) {η κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    (hU : uniformityPower n (fun x ↦ ((f x-g x : ℝ) : ℂ)) ≤ η^(2^(n+1)))
    (herr : ∀ a, (𝔼 t : W, (g (a+t)-h a t)^2) ≤ κ^2) :
    (𝔼 x : G, f x)-η-κ ≤ 𝔼 a : G, 𝔼 t : W, h a t := by
  have h₁ := (abs_le.mp (mean_difference_of_uniformity n f g hη hU)).2
  have h₂ := (abs_le.mp (averaged_local_mean_difference W hW g h hκ herr)).2
  linarith

#print axioms mean_power_le_uniformity
#print axioms local_factor_mean_lower
end Erdos3LocalFactorMean
