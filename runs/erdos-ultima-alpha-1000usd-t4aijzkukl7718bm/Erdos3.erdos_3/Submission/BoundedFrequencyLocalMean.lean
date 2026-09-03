import Submission.BoundedFrequencyLocalCircleCounting

/-! Model-mean transfer with bounded-frequency tests and cutoff-controlled
Fourier mass. The grid modulus contributes only an inverse-modulus error. -/
namespace Erdos3BoundedFrequencyLocalMean
open Finset Erdos3BoundedFrequencyLocalCircleCounting Erdos3BoundedFrequencyPhaseApproximation
  Erdos3SparseFourierModelTransfer Erdos3FiniteFrequencyCoordinates Erdos3BoundedFrequencyObservable
  Erdos3LocalCircleFactorMean Erdos3LocalCircleFactorCounting Erdos3FiniteCircleGrid
  Erdos3StableMaskedUniformity Erdos3FiniteUniformity Erdos3CorrelationSifting
  Erdos3FiniteFourier Erdos3FourierMultilinearTransfer
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
variable {F I : Type*} [Field F] [Fintype F] [Fintype I] [DecidableEq I]
  {N K : ℕ} [NeZero N]

lemma cutoffObservable_fourierMass_le (hKN : K+1 ≤ N)
    (H : (I → ℂ) → ℝ) (hH : ∀ v, 0 ≤ H v ∧ H v ≤ 1) :
    fourierMass (fun y : I → ZMod N ↦ (cutoffObservable K H y : ℂ)) ≤ (K+1 : ℝ)^(Fintype.card I) := by
  apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity)
  have h := cutoffObservable_fourierMass hKN H hH
  simpa only [← pow_mul,mul_comm (Fintype.card I) 4] using h

lemma frequency_local_model_mean (R : ℕ) (W : Finset F) (hW : W.Nonempty)
    (q : F → I → ZMod N) (Φ : (I → ZMod N) → ℝ)
    (hs : ∀ χ, ¬ HasFrequencyBound R χ → hat (fun y ↦ (Φ y : ℂ)) χ = 0)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hU : ∀ χ : AddChar (I → ZMod N) ℂ, HasFrequencyBound R χ → χ ≠ 1 →
      uniformityPower 1 (mask W (fun x ↦ χ (q x))) ≤ θ^4) :
    |(𝔼 t : W, Φ (q t))-(𝔼 y : I → ZMod N, Φ y)| ≤
      (θ/density W)*fourierMass (fun y ↦ (Φ y : ℂ)) := by
  letI : Nonempty W := hW.to_subtype
  have hd (χ : AddChar (I → ZMod N) ℂ) (hχ : HasFrequencyBound R χ) :
      ‖(𝔼 t : W, χ (q t))-(𝔼 y : I → ZMod N, χ y)‖ ≤ θ/density W := by
    by_cases h1 : χ = 1
    · simp only [h1,AddChar.one_apply,Fintype.expect_const,sub_self,norm_zero]
      exact div_nonneg hθ (density_nonneg W)
    · rw [AddChar.expect_eq_zero_iff_ne_zero.mpr h1,sub_zero]
      exact masked_character_mean W hW q χ hθ (hU χ hχ h1)
  have h := sparse_multilinear_transfer_real (J := Unit) (fun _ ↦ Φ)
    (fun (t : W) (_ : Unit) ↦ q t) (fun (y : I → ZMod N) (_ : Unit) ↦ y)
    (fun χ hχ ↦ by
      have hf : HasFrequencyBound R (χ ()) := by
        by_contra hn
        exact hχ () (hs (χ ()) hn)
      simpa only [Fintype.prod_unique] using hd (χ ()) hf)
  simpa only [Fintype.prod_unique] using h

noncomputable def cutoffMeanError (K N m : ℕ) (L : NNReal) (σ θ dW : ℝ) : ℝ :=
  (L : ℝ)*(m : ℝ)*σ+(L : ℝ)*(8/(N : ℝ))+(θ/dW)*(K+1 : ℝ)^m

noncomputable def cutoffCountError (K N m z : ℕ) (L : NNReal) (σ θ dW dB : ℝ) : ℝ :=
  (θ/(dW*dB)+3/(z : ℝ))*(K+1 : ℝ)^(4*m)+4/(z : ℝ)+
    6*(L : ℝ)*(m : ℝ)*σ+96*(L : ℝ)/(N : ℝ)

theorem bounded_frequency_circle_mean (hKN : K+1 ≤ N) (W : Finset F) (hW : W.Nonempty)
    (Q : I → F → ℂ) (hQ : ∀ i x, ‖Q i x‖ = 1)
    (H : (I → ℂ) → ℝ) (hH : ∀ v, 0 ≤ H v ∧ H v ≤ 1)
    {L : NNReal} (hLip : LipschitzWith L H) {σ θ : ℝ} (hσ : 0 ≤ σ) (hθ : 0 ≤ θ)
    (hscale : 2/(K+1 : ℝ) ≤ σ^2)
    (hU : ∀ χ : AddChar (I → ZMod N) ℂ, HasFrequencyBound (4*K) χ → χ ≠ 1 →
      uniformityPower 1 (mask W (fun x ↦ χ (roundedFactor Q x))) ≤ θ^4) :
    |(𝔼 t : W, H (fun i ↦ Q i t))-(𝔼 y : I → ZMod N, H (gridVector y))| ≤
      cutoffMeanError K N (Fintype.card I) L σ θ (density W) := by
  letI : Nonempty W := hW.to_subtype
  let Φ : (I → ZMod N) → ℝ := cutoffObservable K H
  have happrox : |(𝔼 t : W, H (fun i ↦ Q i t))-(𝔼 t : W, Φ (roundedFactor Q t))| ≤
      (L : ℝ)*(Fintype.card I : ℝ)*σ+(L : ℝ)*(8/(N : ℝ)) := by
    rw [← expect_sub_distrib]
    apply (Finset.abs_expect_le _ _).trans
    apply expect_le univ_nonempty
    intro t _
    rw [abs_sub_comm]
    exact cutoffObservable_rounding_error hKN H hLip hσ hscale (fun i ↦ Q i t) (fun i ↦ hQ i t)
  have hm := frequency_local_model_mean K W hW (roundedFactor Q) Φ (cutoffObservable_hat_support K H)
    hθ (fun χ hf hχ ↦ hU χ (frequency_bound_mono (by omega) hf) hχ)
  have hmean : (𝔼 y : I → ZMod N, Φ y) = 𝔼 y : I → ZMod N, H (gridVector y) := cutoffObservable_mean K H
  rw [hmean] at hm
  have hmass := mul_le_mul_of_nonneg_left (cutoffObservable_fourierMass_le hKN H hH)
    (div_nonneg hθ (density_nonneg W))
  have ht := (abs_sub_le _ (𝔼 t : W, Φ (roundedFactor Q t)) _).trans (add_le_add happrox hm)
  unfold cutoffMeanError
  linarith

/-- Reusable conversion from exact bounded integer products to rounded
bounded-frequency character uniformity. -/
theorem rounded_frequency_U2_of_exact (R : ℕ) (W : Finset F)
    (Q : I → F → ℂ) (hQ : ∀ i x, ‖Q i x‖ = 1) {θ : ℝ}
    (hround : 32*density W*(Fintype.card I : ℝ)*(R : ℝ)/(N : ℝ) ≤ θ^4/2)
    (hU : ∀ k : I → ℤ, (∀ i, |k i| ≤ R) → (∃ i, k i ≠ 0) →
      uniformityPower 1 (mask W (fun x ↦ integerPhase k (fun i ↦ Q i x))) ≤ θ^4/2)
    (χ : AddChar (I → ZMod N) ℂ) (hfreq : HasFrequencyBound R χ) (hχ : χ ≠ 1) :
    uniformityPower 1 (mask W (fun x ↦ χ (roundedFactor Q x))) ≤ θ^4 := by
  obtain ⟨k,hk,rfl⟩ := hfreq
  have hkne : ∃ i, k i ≠ 0 := by
    by_contra! hn
    apply hχ
    ext x
    simp only [integerCharacter_apply,hn,zpow_zero,prod_const_one,AddChar.one_apply]
  have hp := (abs_le.mp (rounded_integer_U2_error (N := N) W Q hQ k hk)).2
  have hu := hU k hk hkne
  change uniformityPower 1 (mask W (fun x ↦ integerCharacter k (fun i ↦ roundPhase N (Q i x)))) ≤ _
  linarith

#print axioms bounded_frequency_circle_mean
#print axioms rounded_frequency_U2_of_exact
end Erdos3BoundedFrequencyLocalMean
