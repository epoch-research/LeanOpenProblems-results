import Submission.CyclicStabilityParameters

/-! An explicit polynomial stability modulus in every degree for finite cyclic
groups. This still requires uniformity near its maximum of one. -/
namespace Erdos3QuantitativeCyclicInverse
open Finset Erdos3CyclicStabilityParameters Erdos3DenseDerivativeIntegration
  Erdos3PhaseApproximationAverages Erdos3HigherUniformityPerturbation
  Erdos3HigherUniformityDefect Erdos3HigherPolynomialSeparation
  Erdos3HigherPhaseDifferences Erdos3HigherLocalPolynomialProgressions
  Erdos3FiniteUniformity Erdos3DensePolynomialCocycle Erdos3PolynomialDerivativeConsistency
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

/-- Explicit degree-only power-law threshold for unit phases. The exponent is
2^(n+2)-2, and the coefficient is the dyadic constant 2^(-stabilityCost n). -/
theorem quantitative_cyclic_phase_inverse (n p : ℕ) [NeZero p]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (q : ZMod p → Additive Circle)
    (hU : 1-phaseTolerance n ε ≤ uniformityPower n (fun x ↦ phase (q x))) :
    ∃ r : ZMod p → Additive Circle, IsLocallyPolynomial Set.univ n r ∧
      meanDistance (fun x ↦ phase (q x)) (fun x ↦ phase (r x)) ≤ ε := by
  induction n generalizing ε q with
  | zero =>
    obtain ⟨c,hc⟩ := constant_phase_approximation q
    refine ⟨fun _ ↦ c,global_polynomial_const 0 c,?_⟩
    rw [phaseTolerance_zero] at hU
    change 1-ε^2/2 ≤ ‖phaseMean q‖^2 at hU
    nlinarith only [hc,hU,hε]
  | succ n ih =>
    let η := derivativeAccuracy n ε
    let τ := phaseTolerance n η
    let b : ℝ := ε^2/16
    have hη : 0 < η := derivativeAccuracy_pos n hε
    have hτ : 0 < τ := phaseTolerance_pos n hη
    obtain ⟨hη1,hηgap,hb8,herror⟩ := stability_parameter_bounds n hε hε1
    change 4*η+2*b ≤ ε^2 at herror
    rw [phaseTolerance_succ] at hU
    let v : ZMod p → ℝ := fun h ↦ uniformityPower n (derivative (fun x ↦ phase (q x)) h)
    let S : Finset (ZMod p) := univ.filter (fun h ↦ 1-τ ≤ v h)
    have hv (h : ZMod p) : v h ≤ 1 := uniformityPower_le_one n _
      (derivative_norm_le_one _ (fun x ↦ (phase_norm (q x)).le) h)
    have hmass : τ*badMass S ≤ b*τ := high_values_badMass v hv hU
    have hmassb : badMass S ≤ b := by nlinarith only [hmass,hτ]
    have hS : 4*(Fintype.card (ZMod p)-S.card) < Fintype.card (ZMod p) :=
      dense_of_badMass_le_eighth S (hmassb.trans hb8)
    have hex (h : ZMod p) : ∃ P : ZMod p → Additive Circle, h ∈ S →
        IsLocallyPolynomial Set.univ n P ∧
        meanDistance (fun x ↦ phase (fwdDiff h q x)) (fun x ↦ phase (P x)) ≤ η := by
      by_cases hh : h ∈ S
      · have hvh : 1-τ ≤ uniformityPower n (fun x ↦ phase (fwdDiff h q x)) := by
          rw [phase_fwdDiff]
          exact (mem_filter.mp hh).2
        obtain ⟨P,hP,ha⟩ := ih η hη hη1 (fwdDiff h q) hvh
        exact ⟨P,fun _ ↦ ⟨hP,ha⟩⟩
      · exact ⟨fun _ ↦ 0,fun he ↦ (hh he).elim⟩
    choose P hP using hex
    obtain ⟨r,hr,hd⟩ := dense_derivatives_integrate p n S hS q P hη.le hηgap
      (fun h hh ↦ (hP h hh).1) (fun h hh ↦ (hP h hh).2)
    exact ⟨r,hr,by nlinarith only [hd,hmassb,herror,hε]⟩

noncomputable def boundedTolerance (n : ℕ) (ε : ℝ) : ℝ :=
  phaseTolerance n (ε/2)/(2 : ℝ)^(n+2)

lemma boundedTolerance_pos (n : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < boundedTolerance n ε :=
  div_pos (phaseTolerance_pos n (by linarith only [hε])) (pow_pos (by norm_num) _)

/-- Explicit stability for arbitrary one-bounded complex functions. -/
theorem quantitative_cyclic_inverse (n p : ℕ) [NeZero p]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (f : ZMod p → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1)
    (hU : 1-boundedTolerance n ε ≤ uniformityPower n f) :
    ∃ r : ZMod p → Additive Circle, IsLocallyPolynomial Set.univ n r ∧
      meanDistance f (fun x ↦ phase (r x)) ≤ ε := by
  let δ := boundedTolerance n ε
  let τ := phaseTolerance n (ε/2)
  have hτ : 0 < τ := phaseTolerance_pos n (by linarith only [hε])
  have hpow1 : 1 ≤ (2 : ℝ)^(n+2) := one_le_pow₀ (by norm_num)
  have hδε : δ ≤ ε/2 := by
    calc
      _ ≤ τ := div_le_self hτ.le hpow1
      _ ≤ _ := phaseTolerance_le n (by linarith only [hε]) (by linarith only [hε1])
  have hmult : (1+(2 : ℝ)^(n+1))*δ ≤ τ := by
    have hpc : 1+(2 : ℝ)^(n+1) ≤ 2^(n+2) := by
      have hh : 1 ≤ (2 : ℝ)^(n+1) := one_le_pow₀ (by norm_num)
      rw [show n+2 = (n+1)+1 by omega,pow_succ (2 : ℝ) (n+1)]
      linarith only [hh]
    have hd : 0 ≤ δ := (boundedTolerance_pos n hε).le
    calc
      _ ≤ (2 : ℝ)^(n+2)*δ := mul_le_mul_of_nonneg_right hpc hd
      _ = τ := by dsimp only [δ,boundedTolerance,τ]; field_simp
  let q := radialPhase f
  have hdist : meanDistance f (fun x ↦ phase (q x)) ≤ δ := by
    rw [radialPhase_meanDistance f hf]
    linarith only [hU,uniformity_le_mean_norm n f hf]
  have hpert := uniformity_lipschitz n f (fun x ↦ phase (q x)) hf (fun x ↦ (phase_norm _).le)
  have hle := (le_abs_self (uniformityPower n f-uniformityPower n (fun x ↦ phase (q x)))).trans hpert
  have hm := mul_le_mul_of_nonneg_left hdist (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n+1))
  have hqU : 1-τ ≤ uniformityPower n (fun x ↦ phase (q x)) := by
    nlinarith only [hU,hle,hm,hmult]
  obtain ⟨r,hr,ha⟩ := quantitative_cyclic_phase_inverse n p (ε/2)
    (by linarith only [hε]) (by linarith only [hε1]) q hqU
  refine ⟨r,hr,?_⟩
  have ht := meanDistance_triangle f (fun x ↦ phase (q x)) (fun x ↦ phase (r x))
  linarith only [ht,hdist,hδε,ha]

#print axioms quantitative_cyclic_phase_inverse
#print axioms quantitative_cyclic_inverse
end Erdos3QuantitativeCyclicInverse
