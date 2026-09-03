import Submission.LocalCircleFactorCounting
import Submission.LocalFactorMean

/-! Distribution of rounded local factors also controls their means. This
connects the finite model's density to the actual density of the original
circle-valued local factor, with all grid and masking errors explicit. -/
namespace Erdos3LocalCircleFactorMean
open Finset Erdos3LocalCircleFactorCounting Erdos3ApproximateLocalQuadraticCounting
  Erdos3LocalQuadraticDistribution Erdos3FiniteCircleGrid Erdos3StableMaskedUniformity
  Erdos3LocalFactorMean Erdos3FiniteUniformity Erdos3CorrelationSifting
  Erdos3FourierMultilinearTransfer Erdos3RelativeStableBohr Erdos3FiniteBohr
  Erdos3StableWindowCounting Erdos3LocalQuadraticInverse
open scoped BigOperators Classical
set_option maxHeartbeats 6000000

variable {F G : Type*} [Field F] [Fintype F] [AddCommGroup G] [Fintype G]

lemma masked_character_mean (W : Finset F) (hW : W.Nonempty) (q : F → G)
    (χ : AddChar G ℂ) {η : ℝ} (hη : 0 ≤ η)
    (hU : uniformityPower 1 (mask W (fun x ↦ χ (q x))) ≤ η^4) :
    ‖𝔼 t : W, χ (q t)‖ ≤ η/density W := by
  have hp := density_pos W hW
  have hnorm : ‖𝔼 x : F, mask W (fun x ↦ χ (q x)) x‖ ≤ η := by
    apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) hη
    exact (mean_power_le_uniformity 1 (mask W (fun x ↦ χ (q x)))).trans hU
  have he : (𝔼 x : F, mask W (fun x ↦ χ (q x)) x) =
      (density W : ℂ)*(𝔼 t : W, χ (q t)) := by
    rw [supported_expect W hW _ (fun x hx ↦ by simp only [mask,if_neg hx])]
    congr 1
    apply expect_congr rfl
    intro t _
    exact if_pos t.property
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp] at hnorm
  exact (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hnorm)

/-- Arbitrary real observables transfer from a local factor to the uniform
finite target, with loss equal to their Fourier L1 mass. -/
theorem local_model_mean_difference (W : Finset F) (hW : W.Nonempty) (q : F → G)
    (Φ : G → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hU : ∀ χ : AddChar G ℂ, χ ≠ 1 →
      uniformityPower 1 (mask W (fun x ↦ χ (q x))) ≤ η^4) :
    |(𝔼 t : W, Φ (q t))-(𝔼 y : G, Φ y)| ≤
      (η/density W)*fourierMass (fun y ↦ (Φ y : ℂ)) := by
  letI : Nonempty W := hW.to_subtype
  have hd (χ : AddChar G ℂ) :
      ‖(𝔼 t : W, χ (q t))-(𝔼 y : G, χ y)‖ ≤ η/density W := by
    by_cases hχ : χ = 1
    · simp only [hχ,AddChar.one_apply,Fintype.expect_const,sub_self,norm_zero]
      exact div_nonneg hη (density_nonneg W)
    · rw [AddChar.expect_eq_zero_iff_ne_zero.mpr hχ,sub_zero]
      exact masked_character_mean W hW q χ hη (hU χ hχ)
  have h := multilinear_transfer_real (I := Unit) (fun _ ↦ Φ)
    (fun (t : W) (_ : Unit) ↦ q t) (fun (y : G) (_ : Unit) ↦ y)
    (fun χ ↦ by simpa only [Fintype.prod_unique] using hd (χ ()))
  simpa only [Fintype.prod_unique] using h

variable {I : Type*} [Fintype I] {N : ℕ} [NeZero N]

/-- The model mean differs from the mean of the actual circle factor by the
grid error plus the single-character distribution error. -/
theorem local_circle_mean_difference (W : Finset F) (hW : W.Nonempty)
    (Q : I → F → ℂ) (hQ : ∀ i x, ‖Q i x‖ = 1)
    (H : (I → ℂ) → ℝ) {L : NNReal} (hLip : LipschitzWith L H)
    {η : ℝ} (hη : 0 ≤ η)
    (hU : ∀ χ : AddChar (I → ZMod N) ℂ, χ ≠ 1 →
      uniformityPower 1 (mask W (fun x ↦ χ (roundedFactor Q x))) ≤ η^4) :
    |(𝔼 t : W, H (fun i ↦ Q i t))-(𝔼 y : I → ZMod N, H (gridVector y))| ≤
      (L : ℝ)*(8/(N : ℝ))+(η/density W)*fourierMass (fun y : I → ZMod N ↦ (H (gridVector y) : ℂ)) := by
  letI : Nonempty W := hW.to_subtype
  have hgrid : |(𝔼 t : W, H (fun i ↦ Q i t))-
      (𝔼 t : W, gridObservable (N := N) H (roundedFactor Q t))| ≤ (L : ℝ)*(8/(N : ℝ)) := by
    rw [← expect_sub_distrib]
    apply (Finset.abs_expect_le _ _).trans
    apply expect_le univ_nonempty
    intro t _
    rw [abs_sub_comm]
    exact gridObservable_error H hLip (fun i ↦ Q i t) (fun i ↦ hQ i t)
  have hmodel := local_model_mean_difference W hW (roundedFactor Q) (gridObservable H) hη hU
  exact (abs_sub_le _ (𝔼 t : W, gridObservable (N := N) H (roundedFactor Q t)) _).trans
    (add_le_add hgrid hmodel)

/-- A density-based form of the local circle count. The mean used on the left
is the actual local factor mean, not an independently assumed model density. -/
theorem local_circle_count_of_mean (B : Finset F) (hB : B.Nonempty)
    (hv : Function.Injective (fun j : Fin 4 ↦ (j.val : F)))
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (hs : ∀ b c : B, ∀ j : Fin 4,
      (j.val : F)*((c : F)-b) ∈ bohr C (relativeWidth C z r))
    (Q : I → F → ℂ) (hQ : ∀ i x, ‖Q i x‖ = 1)
    (hpoly : ∀ i, IsLocallyQuadratic (bohr C r : Set F) (Q i))
    (H : (I → ℂ) → ℝ) (hH : ∀ v, 0 ≤ H v ∧ H v ≤ 1)
    {L : NNReal} (hLip : LipschitzWith L H) {η α : ℝ} (hη : 0 ≤ η) (hα : 0 ≤ α)
    (hU : ∀ χ : AddChar (I → ZMod N) ℂ, χ ≠ 1 →
      uniformityPower 1 (mask (bohr C r) (fun x ↦ χ (roundedFactor Q x))) ≤ η^4)
    (hmean : α ≤ 𝔼 t : bohr C r, H (fun i ↦ Q i t))
    (hbudget : (L : ℝ)*(8/(N : ℝ))+(η/density (bohr C r))*
      fourierMass (fun y : I → ZMod N ↦ (H (gridVector y) : ℂ)) ≤ α/2) :
    (α/2)^4-
      (η/(density (bohr C r)*density B)+3/(z : ℝ))*(N : ℝ)^(2*Fintype.card I)-
      4/(z : ℝ)-96*(L : ℝ)/(N : ℝ) ≤
      windowPatternAverage (bohr C r)
        (fun (p : B × B) (j : Fin 4) ↦ (j.val : F)*((p.2 : F)-p.1))
        (fun t ↦ H (fun i ↦ Q i t)) := by
  have hm := (abs_le.mp (local_circle_mean_difference (bohr C r) ⟨0,bohr_zero C hr.le⟩
    Q hQ H hLip hη hU)).2
  have hhalf : α/2 ≤ 𝔼 y : I → ZMod N, H (gridVector y) := by linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ α/2) hhalf 4
  have hc := local_circle_count B hB hv C hr hz hstable hs Q hQ hpoly H hH hLip hη hU
  linarith

#print axioms local_circle_mean_difference
#print axioms local_circle_count_of_mean
end Erdos3LocalCircleFactorMean
