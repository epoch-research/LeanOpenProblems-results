import Submission.BoundedFrequencyLocalMean

/-! Averaged actual local counting from bounded exact phase combinations.
The criterion tests a fixed finite integer-frequency box, independently of
the auxiliary grid modulus used in the proof. -/
namespace Erdos3AveragedExactPhaseCounting
open Finset Erdos3BoundedFrequencyLocalMean Erdos3BoundedFrequencyLocalCircleCounting
  Erdos3BoundedFrequencyPhaseApproximation Erdos3FiniteFrequencyCoordinates
  Erdos3LocalCircleFactorCounting Erdos3FiniteCircleGrid Erdos3StableMaskedUniformity
  Erdos3FiniteUniformity Erdos3CorrelationSifting Erdos3RelativeStableBohr Erdos3FiniteBohr
  Erdos3StableWindowCounting Erdos3LocalQuadraticInverse Erdos3FiniteSamplingMoments
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
variable {F I X : Type*} [Field F] [Fintype F] [Fintype I] [DecidableEq I]
  [Fintype X] [Nonempty X] {N K : ℕ} [NeZero N]

theorem averaged_exact_phase_count (hKN : K+1 ≤ N) (B : Finset F) (hB : B.Nonempty)
    (hv : Function.Injective (fun j : Fin 4 ↦ (j.val : F)))
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (hs : ∀ b c : B, ∀ j : Fin 4,
      (j.val : F)*((c : F)-b) ∈ bohr C (relativeWidth C z r))
    (Q : X → I → F → ℂ) (hQ : ∀ a i x, ‖Q a i x‖ = 1)
    (hpoly : ∀ a i, IsLocallyQuadratic (bohr C r : Set F) (Q a i))
    (H : X → (I → ℂ) → ℝ) (hH : ∀ a v, 0 ≤ H a v ∧ H a v ≤ 1)
    {L : NNReal} (hLip : ∀ a, LipschitzWith L (H a))
    {θ σ α : ℝ} (hθ : 0 ≤ θ) (hσ : 0 ≤ σ) (hα : 0 ≤ α)
    (hscale : 2/(K+1 : ℝ) ≤ σ^2)
    (hround : 32*density (bohr C r)*(Fintype.card I : ℝ)*(4*K : ℕ)/(N : ℝ) ≤ θ^4/2)
    (hU : ∀ a, ∀ k : I → ℤ, (∀ i, |k i| ≤ (4*K : ℕ)) → (∃ i, k i ≠ 0) →
      uniformityPower 1 (mask (bohr C r) (fun x ↦ integerPhase k (fun i ↦ Q a i x))) ≤ θ^4/2)
    (hmean : α+cutoffMeanError K N (Fintype.card I) L σ θ (density (bohr C r)) ≤
      𝔼 a : X, 𝔼 t : bohr C r, H a (fun i ↦ Q a i t)) :
    α^4-cutoffCountError K N (Fintype.card I) z L σ θ (density (bohr C r)) (density B) ≤
      𝔼 a : X, windowPatternAverage (bohr C r)
        (fun (p : B × B) (j : Fin 4) ↦ (j.val : F)*((p.2 : F)-p.1))
        (fun t ↦ H a (fun i ↦ Q a i t)) := by
  let μ (a : X) : ℝ := 𝔼 y : I → ZMod N, H a (gridVector y)
  have hm (a : X) : (𝔼 t : bohr C r, H a (fun i ↦ Q a i t)) ≤
      μ a+cutoffMeanError K N (Fintype.card I) L σ θ (density (bohr C r)) := by
    have h := (abs_le.mp (bounded_frequency_circle_mean hKN (bohr C r) ⟨0,bohr_zero C hr.le⟩
      (Q a) (hQ a) (H a) (hH a) (hLip a) hσ hθ hscale
      (rounded_frequency_U2_of_exact (4*K) (bohr C r) (Q a) (hQ a) hround (hU a)))).2
    dsimp only [μ]
    linarith
  have hμ : α ≤ 𝔼 a : X, μ a := by
    have h := expect_le_expect (s := univ) (fun a _ ↦ hm a)
    rw [expect_add_distrib,Fintype.expect_const] at h
    linarith
  have hfour : α^4 ≤ 𝔼 a : X, (μ a)^4 :=
    (pow_le_pow_left₀ hα hμ 4).trans (expect_even_pow_le (by decide : Even 4) μ)
  have hc (a : X) : (μ a)^4-cutoffCountError K N (Fintype.card I) z L σ θ
      (density (bohr C r)) (density B) ≤
      windowPatternAverage (bohr C r)
        (fun (p : B × B) (j : Fin 4) ↦ (j.val : F)*((p.2 : F)-p.1))
        (fun t ↦ H a (fun i ↦ Q a i t)) := by
    have h := local_circle_count_from_exact_phases hKN B hB hv C hr hz hstable hs
      (Q a) (hQ a) (hpoly a) (H a) (hH a) (hLip a) hθ hσ hscale hround (hU a)
    dsimp only [μ,cutoffCountError]
    linarith
  have h := expect_le_expect (s := univ) (fun a _ ↦ hc a)
  rw [expect_sub_distrib,Fintype.expect_const] at h
  linarith

#print axioms averaged_exact_phase_count
end Erdos3AveragedExactPhaseCounting
