import Submission.PhaseApproximationAverages

/-! Integrating sufficiently accurate polynomial derivatives on a dense set
of directions produces an L1 approximation by an actual polynomial phase. -/
namespace Erdos3DenseDerivativeIntegration
open Finset Erdos3PhaseApproximationAverages Erdos3PolynomialCocycleIntegration
  Erdos3DensePolynomialCocycle Erdos3PolynomialDerivativeConsistency
  Erdos3HigherUniformityPerturbation Erdos3HigherUniformityDefect
  Erdos3HigherPolynomialSeparation Erdos3HigherPhaseDifferences
  Erdos3HigherPhaseRepresentation Erdos3HigherLocalPolynomialProgressions
  Erdos3FiniteUniformity
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

/-- Quantitative integration on a finite cyclic group. The error is controlled
by both derivative-approximation error and the exceptional fraction of directions. -/
theorem dense_derivatives_integrate (p n : ℕ) [NeZero p] (S : Finset (ZMod p))
    (hS : 4*(Fintype.card (ZMod p)-S.card) < Fintype.card (ZMod p))
    (q : ZMod p → Additive Circle) (P : ZMod p → ZMod p → Additive Circle) {η : ℝ}
    (hη0 : 0 ≤ η) (hη : 3*η < polynomialGap n/2)
    (hpoly : ∀ h ∈ S, IsLocallyPolynomial Set.univ n (P h))
    (happrox : ∀ h ∈ S, meanDistance (fun x ↦ phase (fwdDiff h q x)) (fun x ↦ phase (P h x)) ≤ η) :
    ∃ r : ZMod p → Additive Circle, IsLocallyPolynomial Set.univ (n+1) r ∧
      (meanDistance (fun x ↦ phase (q x)) (fun x ↦ phase (r x)))^2 ≤ 4*η+2*badMass S := by
  obtain ⟨C,hC0,hCgood,hCpoly,hC⟩ := dense_derivative_polynomial_cocycle n S hS q P hη hpoly happrox
  obtain ⟨r,hr0,hr,hpr⟩ := cyclic_polynomial_cocycle_integrates p n C hC0 hCpoly hC
  let u : ZMod p → Additive Circle := fun x ↦ q x-r x
  have hgood (h : ZMod p) (hh : h ∈ S) :
      1-uniformityPower 0 (derivative (fun x ↦ phase (u x)) h) ≤ 2*η := by
    let c := P h 0-fwdDiff h r 0
    have hder (x : ZMod p) : fwdDiff h r x = P h x-P h 0+fwdDiff h r 0 := by
      have he := congr_fun ((hr h).trans (hCgood h hh)) x
      exact sub_eq_iff_eq_add.mp he
    have he (x : ZMod p) : fwdDiff h u x-c = fwdDiff h q x-P h x := by
      have hd : fwdDiff h u x = fwdDiff h q x-fwdDiff h r x := by
        dsimp only [u,fwdDiff]
        abel
      rw [hd,hder]
      dsimp only [c]
      abel
    have hdist : meanDistance (fun x ↦ phase (fwdDiff h u x)) (fun _ ↦ phase c) ≤ η := by
      have hd : meanDistance (fun x ↦ phase (fwdDiff h u x)) (fun _ ↦ phase c) =
          meanDistance (fun x ↦ phase (fwdDiff h q x)) (fun x ↦ phase (P h x)) := by
        unfold meanDistance
        apply expect_congr rfl
        intro x _
        rw [phase_sub_norm,phase_sub_norm,he]
      rw [hd]
      exact happrox h hh
    have hmean := mean_square_of_close_constant (fwdDiff h u) c
    have hm : ‖phaseMean (fwdDiff h u)‖^2 = uniformityPower 0 (derivative (fun x ↦ phase (u x)) h) := by
      unfold phaseMean
      rw [phase_fwdDiff]
      rfl
    rw [hm] at hmean
    linarith only [hmean,hdist]
  have hdefect : 1-uniformityPower 1 (fun x ↦ phase (u x)) ≤ 2*η+badMass S :=
    mean_defect_badMass S (fun h ↦ uniformityPower 0 (derivative (fun x ↦ phase (u x)) h))
      (fun h ↦ uniformityPower_nonneg _ _) (by linarith only [hη0]) hgood
  obtain ⟨χ,c,hχ⟩ := character_phase_approximation u
  let R : ZMod p → Additive Circle := fun x ↦ r x+(characterPhase χ x+c)
  have hRpoly : IsLocallyPolynomial Set.univ (n+1) R :=
    global_polynomial_add (n+1) _ _ hpr
      (global_polynomial_add (n+1) _ _ (characterPhase_polynomial n χ) (global_polynomial_const (n+1) c))
  refine ⟨R,hRpoly,?_⟩
  have hdist : meanDistance (fun x ↦ phase (q x)) (fun x ↦ phase (R x)) =
      meanDistance (fun x ↦ phase (u x)) (fun x ↦ phase (characterPhase χ x+c)) := by
    unfold meanDistance
    exact expect_congr rfl (fun x _ ↦ phase_distance_sub_right _ _ _)
  rw [hdist]
  linarith only [hχ,hdefect]

#print axioms dense_derivatives_integrate
end Erdos3DenseDerivativeIntegration
