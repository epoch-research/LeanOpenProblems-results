import Submission.RectangularSpectralCutoff

/-! Positive bounded-frequency approximations to finite-grid observables.
Their Fourier support and mass are controlled independently of grid size. -/
namespace Erdos3BoundedFrequencyObservable
open Finset Erdos3RectangularSpectralCutoff Erdos3FiniteFrequencyCoordinates
  Erdos3PositiveSpectralSmoothing Erdos3FiniteCircleGrid
  Erdos3ApproximateLocalQuadraticCounting Erdos3FourierMultilinearTransfer
  Erdos3FiniteFourier
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 5000000

variable {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ} [NeZero N]

noncomputable def cutoffObservable (K : ℕ) (H : (I → ℂ) → ℝ) : (I → ZMod N) → ℝ :=
  spectralSmooth (spectralBox K) (gridObservable H)

lemma cutoffObservable_bounds (K : ℕ) (H : (I → ℂ) → ℝ)
    (hH : ∀ v, 0 ≤ H v ∧ H v ≤ 1) (y : I → ZMod N) :
    0 ≤ cutoffObservable K H y ∧ cutoffObservable K H y ≤ 1 :=
  spectralSmooth_bounds (spectralBox (I := I) (N := N) K) (spectralBox_nonempty K) (gridObservable (N := N) H)
    (fun y ↦ hH (gridVector y)) y

lemma cutoffObservable_mean (K : ℕ) (H : (I → ℂ) → ℝ) :
    (𝔼 y : I → ZMod N, cutoffObservable K H y) = 𝔼 y : I → ZMod N, H (gridVector y) :=
  spectralSmooth_mean (spectralBox (I := I) (N := N) K) (spectralBox_nonempty K) (gridObservable (N := N) H)

lemma cutoffObservable_hat_support (K : ℕ) (H : (I → ℂ) → ℝ)
    (χ : AddChar (I → ZMod N) ℂ) (hχ : ¬ HasFrequencyBound K χ) :
    hat (fun y ↦ (cutoffObservable K H y : ℂ)) χ = 0 := by
  apply spectralSmooth_hat_support
  intro hmem
  exact hχ (box_ratio_frequency hmem)

/-- Fourier mass is bounded using the cutoff alone, even as N tends to infinity. -/
theorem cutoffObservable_fourierMass {K : ℕ} (hKN : K+1 ≤ N)
    (H : (I → ℂ) → ℝ) (hH : ∀ v, 0 ≤ H v ∧ H v ≤ 1) :
    fourierMass (fun y : I → ZMod N ↦ (cutoffObservable K H y : ℂ))^4 ≤
      (K+1 : ℝ)^(4*Fintype.card I) := by
  have h := spectralSmooth_fourierMass_four (spectralBox (I := I) (N := N) K) (spectralBox_nonempty K)
    (gridObservable H) (fun y ↦ hH _)
  have hc : ((spectralBox (I := I) (N := N) K/spectralBox K).card : ℝ) ≤
      (K+1 : ℝ)^(2*Fintype.card I) := by exact_mod_cast spectralBox_ratio_card hKN (I := I)
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
  have he : ((K+1 : ℝ)^(2*Fintype.card I))^2 = (K+1 : ℝ)^(4*Fintype.card I) := by
    rw [← pow_mul]
    congr 1
    omega
  exact h.trans (hp.trans_eq he)

theorem cutoffObservable_approximation {K : ℕ} (hKN : K+1 ≤ N)
    (H : (I → ℂ) → ℝ) {L : NNReal} (hLip : LipschitzWith L H)
    {σ : ℝ} (hσ : 0 ≤ σ) (hscale : 2/(K+1 : ℝ) ≤ σ^2) (y : I → ZMod N) :
    |cutoffObservable K H y-H (gridVector y)| ≤ (L : ℝ)*(Fintype.card I : ℝ)*σ := by
  have h := spectralSmooth_approximation (spectralBox (I := I) (N := N) K) (spectralBox_nonempty K)
    coordinateCharacter H hLip (fun _ ↦ σ) (fun _ ↦ hσ)
    (fun i ↦ (spectralBox_boundary hKN i).trans hscale) y
  simpa only [coordinateCharacter_apply,sum_const,card_univ,nsmul_eq_mul,mul_assoc] using h

lemma cutoffObservable_rounding_error {K : ℕ} (hKN : K+1 ≤ N)
    (H : (I → ℂ) → ℝ) {L : NNReal} (hLip : LipschitzWith L H)
    {σ : ℝ} (hσ : 0 ≤ σ) (hscale : 2/(K+1 : ℝ) ≤ σ^2)
    (v : I → ℂ) (hv : ∀ i, ‖v i‖ = 1) :
    |cutoffObservable K H (fun i ↦ roundPhase N (v i))-H v| ≤
      (L : ℝ)*(Fintype.card I : ℝ)*σ+(L : ℝ)*(8/(N : ℝ)) := by
  exact (abs_sub_le _ (H (gridVector (fun i ↦ roundPhase N (v i)))) _).trans
    (add_le_add (cutoffObservable_approximation hKN H hLip hσ hscale _)
      (gridObservable_error H hLip v hv))

lemma cutoffObservable_quadratic_defect {K : ℕ} (hKN : K+1 ≤ N)
    (H : (I → ℂ) → ℝ) {L : NNReal} (hLip : LipschitzWith L H)
    {σ : ℝ} (hσ : 0 ≤ σ) (hscale : 2/(K+1 : ℝ) ≤ σ^2)
    (v : Fin 4 → I → ℂ) (hv : ∀ j i, ‖v j i‖ = 1)
    (hrel : ∀ i, v 3 i = quadraticWord (v 0 i) (v 1 i) (v 2 i)) :
    |cutoffObservable K H (fun i ↦ roundPhase N (v 3 i))-
      cutoffObservable K H ((fun i ↦ roundPhase N (v 0 i))-
        3 • (fun i ↦ roundPhase N (v 1 i))+3 • (fun i ↦ roundPhase N (v 2 i)))| ≤
      2*((L : ℝ)*(Fintype.card I : ℝ)*σ)+(L : ℝ)*(64/(N : ℝ)) := by
  let a : I → ZMod N := fun i ↦ roundPhase N (v 3 i)
  let b : I → ZMod N := (fun i ↦ roundPhase N (v 0 i))-
        3 • (fun i ↦ roundPhase N (v 1 i))+3 • (fun i ↦ roundPhase N (v 2 i))
  have ha := cutoffObservable_approximation hKN H hLip hσ hscale a
  have hb := cutoffObservable_approximation hKN H hLip hσ hscale b
  have hd := gridObservable_defect (N := N) H hLip v hv hrel
  have ht := (abs_sub_le (cutoffObservable K H a) (H (gridVector a)) (cutoffObservable K H b)).trans
    (add_le_add le_rfl (abs_sub_le (H (gridVector a)) (H (gridVector b)) (cutoffObservable K H b)))
  rw [abs_sub_comm (H (gridVector b))] at ht
  change |H (gridVector a)-H (gridVector b)| ≤ _ at hd
  linarith

#print axioms cutoffObservable_fourierMass
#print axioms cutoffObservable_quadratic_defect
end Erdos3BoundedFrequencyObservable
