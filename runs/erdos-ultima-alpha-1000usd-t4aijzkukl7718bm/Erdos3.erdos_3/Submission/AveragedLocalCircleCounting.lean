import Submission.LocalCircleFactorMean

/-! Averaging the local model means before applying the fourth-moment bound
allows different local phases and observables at every base point. All
complexities and all counting errors are uniform and explicit. -/
namespace Erdos3AveragedLocalCircleCounting
open Finset Erdos3LocalCircleFactorMean Erdos3LocalCircleFactorCounting
  Erdos3ApproximateLocalQuadraticCounting Erdos3FiniteCircleGrid
  Erdos3StableMaskedUniformity Erdos3FiniteUniformity Erdos3CorrelationSifting
  Erdos3FourierMultilinearTransfer Erdos3RelativeStableBohr Erdos3FiniteBohr
  Erdos3StableWindowCounting Erdos3LocalQuadraticInverse Erdos3DerivativeSpectrum
  Erdos3FiniteSamplingMoments
open scoped BigOperators Classical
set_option maxHeartbeats 6000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma bounded_fourierMass_le_card (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    fourierMass f ≤ (Fintype.card G : ℝ) := by
  unfold fourierMass
  calc
    _ ≤ ∑ _χ : AddChar G ℂ, (1 : ℝ) := sum_le_sum (fun χ _ ↦ norm_hat_le_one f hf χ)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,AddChar.card_eq]

variable {F I X : Type*} [Field F] [Fintype F] [Fintype I]
  [Fintype X] [Nonempty X] {N : ℕ} [NeZero N]

noncomputable def modelMeanError (N m : ℕ) (L : NNReal) (θ d : ℝ) : ℝ :=
  (L : ℝ)*(8/(N : ℝ))+(θ/d)*(N : ℝ)^m

noncomputable def modelCountError (N m z : ℕ) (L : NNReal) (θ dW dB : ℝ) : ℝ :=
  (θ/(dW*dB)+3/(z : ℝ))*(N : ℝ)^(2*m)+4/(z : ℝ)+96*(L : ℝ)/(N : ℝ)

/-- The averaged local count is controlled by the averaged actual local mean,
not by the minimum mean among base points. -/
theorem averaged_circle_count (B : Finset F) (hB : B.Nonempty)
    (hv : Function.Injective (fun j : Fin 4 ↦ (j.val : F)))
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (hs : ∀ b c : B, ∀ j : Fin 4,
      (j.val : F)*((c : F)-b) ∈ bohr C (relativeWidth C z r))
    (Q : X → I → F → ℂ) (hQ : ∀ a i x, ‖Q a i x‖ = 1)
    (hpoly : ∀ a i, IsLocallyQuadratic (bohr C r : Set F) (Q a i))
    (H : X → (I → ℂ) → ℝ) (hH : ∀ a v, 0 ≤ H a v ∧ H a v ≤ 1)
    {L : NNReal} (hLip : ∀ a, LipschitzWith L (H a)) {θ α : ℝ} (hθ : 0 ≤ θ) (hα : 0 ≤ α)
    (hU : ∀ a, ∀ χ : AddChar (I → ZMod N) ℂ, χ ≠ 1 →
      uniformityPower 1 (mask (bohr C r) (fun x ↦ χ (roundedFactor (Q a) x))) ≤ θ^4)
    (hmean : α+modelMeanError N (Fintype.card I) L θ (density (bohr C r)) ≤
      𝔼 a : X, 𝔼 t : bohr C r, H a (fun i ↦ Q a i t)) :
    α^4-modelCountError N (Fintype.card I) z L θ (density (bohr C r)) (density B) ≤
      𝔼 a : X, windowPatternAverage (bohr C r)
        (fun (p : B × B) (j : Fin 4) ↦ (j.val : F)*((p.2 : F)-p.1))
        (fun t ↦ H a (fun i ↦ Q a i t)) := by
  let μ (a : X) : ℝ := 𝔼 y : I → ZMod N, H a (gridVector y)
  have hm (a : X) : (𝔼 t : bohr C r, H a (fun i ↦ Q a i t)) ≤
      μ a+modelMeanError N (Fintype.card I) L θ (density (bohr C r)) := by
    have ht := (abs_le.mp (local_circle_mean_difference (bohr C r) ⟨0,bohr_zero C hr.le⟩
      (Q a) (hQ a) (H a) (hLip a) hθ (hU a))).2
    have hmass := bounded_fourierMass_le_card (fun y : I → ZMod N ↦ (H a (gridVector y) : ℂ))
      (fun y ↦ by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hH a _).1] using (hH a _).2)
    rw [Fintype.card_fun,ZMod.card,Nat.cast_pow] at hmass
    have hl := mul_le_mul_of_nonneg_left hmass (div_nonneg hθ (density_nonneg (bohr C r)))
    dsimp only [μ,modelMeanError]
    linarith
  have hμ : α ≤ 𝔼 a : X, μ a := by
    have hh := expect_le_expect (s := univ) (fun a _ ↦ hm a)
    rw [expect_add_distrib,Fintype.expect_const] at hh
    linarith
  have hfour : α^4 ≤ 𝔼 a : X, (μ a)^4 :=
    (pow_le_pow_left₀ hα hμ 4).trans (expect_even_pow_le (by decide : Even 4) μ)
  have hc (a : X) : (μ a)^4-modelCountError N (Fintype.card I) z L θ
      (density (bohr C r)) (density B) ≤
      windowPatternAverage (bohr C r)
        (fun (p : B × B) (j : Fin 4) ↦ (j.val : F)*((p.2 : F)-p.1))
        (fun t ↦ H a (fun i ↦ Q a i t)) := by
    have h := local_circle_count B hB hv C hr hz hstable hs (Q a) (hQ a) (hpoly a)
      (H a) (hH a) (hLip a) hθ (hU a)
    dsimp only [μ,modelCountError]
    linarith
  have hh := expect_le_expect (s := univ) (fun a _ ↦ hc a)
  rw [expect_sub_distrib,Fintype.expect_const] at hh
  linarith

#print axioms averaged_circle_count
end Erdos3AveragedLocalCircleCounting
