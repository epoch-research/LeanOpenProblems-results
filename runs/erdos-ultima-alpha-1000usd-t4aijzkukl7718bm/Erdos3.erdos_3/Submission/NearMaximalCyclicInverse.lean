import Submission.DenseDerivativeIntegration

/-! A dimension-free 99-percent inverse theorem in every degree on finite
cyclic groups. The uniformity threshold is uniform in the modulus, but is
near one; this is not an inverse theorem for a small positive lower bound. -/
namespace Erdos3NearMaximalCyclicInverse
open Finset Erdos3DenseDerivativeIntegration Erdos3PhaseApproximationAverages
  Erdos3HigherUniformityPerturbation Erdos3HigherUniformityDefect
  Erdos3HigherPolynomialSeparation Erdos3HigherPhaseDifferences
  Erdos3HigherLocalPolynomialProgressions Erdos3FiniteUniformity
  Erdos3DensePolynomialCocycle Erdos3PolynomialDerivativeConsistency
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

/-- Near-maximal higher uniformity of a circle phase implies approximation by
an exact polynomial phase. The tolerance depends only on degree and error. -/
theorem near_maximal_cyclic_phase_inverse (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℕ, ∀ _ : NeZero p, ∀ q : ZMod p → Additive Circle,
      1-δ ≤ uniformityPower n (fun x ↦ phase (q x)) →
      ∃ r : ZMod p → Additive Circle, IsLocallyPolynomial Set.univ n r ∧
        meanDistance (fun x ↦ phase (q x)) (fun x ↦ phase (r x)) ≤ ε := by
  induction n generalizing ε with
  | zero =>
    refine ⟨ε^2/2,by positivity,?_⟩
    intro p hp q hU
    obtain ⟨c,hc⟩ := constant_phase_approximation q
    refine ⟨fun _ ↦ c,global_polynomial_const 0 c,?_⟩
    change 1-ε^2/2 ≤ ‖phaseMean q‖^2 at hU
    nlinarith only [hc,hU,hε]
  | succ n ih =>
    let η : ℝ := min (polynomialGap n/12) (ε^2/16)
    let b : ℝ := min (1/8) (ε^2/8)
    have hη : 0 < η := lt_min (div_pos (polynomialGap_pos n) (by norm_num)) (by positivity)
    have hb : 0 < b := lt_min (by norm_num) (by positivity)
    have hηgap : 3*η < polynomialGap n/2 := by
      have hh : η ≤ polynomialGap n/12 := min_le_left _ _
      have hg := polynomialGap_pos n
      linarith only [hh,hg]
    have hηε : η ≤ ε^2/16 := min_le_right _ _
    have hbε : b ≤ ε^2/8 := min_le_right _ _
    have hb8 : b ≤ 1/8 := min_le_left _ _
    obtain ⟨τ,hτ,hτinv⟩ := ih η hη
    refine ⟨b*τ,mul_pos hb hτ,?_⟩
    intro p hp q hU
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
        obtain ⟨P,hP,ha⟩ := hτinv p hp (fwdDiff h q) hvh
        exact ⟨P,fun _ ↦ ⟨hP,ha⟩⟩
      · exact ⟨fun _ ↦ 0,fun he ↦ (hh he).elim⟩
    choose P hP using hex
    obtain ⟨r,hr,hd⟩ := dense_derivatives_integrate p n S hS q P hη.le hηgap
      (fun h hh ↦ (hP h hh).1) (fun h hh ↦ (hP h hh).2)
    refine ⟨r,hr,?_⟩
    have hbound : 4*η+2*badMass S ≤ ε^2 := by linarith only [hηε,hmassb,hbε,sq_nonneg ε]
    nlinarith only [hd,hbound,hε]

/-- The same inverse statement for all one-bounded complex functions. Radial
normalization is quantitatively controlled; zero values are not discarded. -/
theorem near_maximal_cyclic_inverse (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℕ, ∀ _ : NeZero p, ∀ f : ZMod p → ℂ,
      (∀ x, ‖f x‖ ≤ 1) → 1-δ ≤ uniformityPower n f →
      ∃ r : ZMod p → Additive Circle, IsLocallyPolynomial Set.univ n r ∧
        meanDistance f (fun x ↦ phase (r x)) ≤ ε := by
  obtain ⟨τ,hτ,hphase⟩ := near_maximal_cyclic_phase_inverse n (ε/2) (by linarith only [hε])
  let C : ℝ := 1+2^(n+1)
  have hC : 0 < C := by dsimp only [C]; positivity
  let δ : ℝ := min (ε/2) (τ/C)
  have hδ : 0 < δ := lt_min (by linarith only [hε]) (div_pos hτ hC)
  have hδε : δ ≤ ε/2 := min_le_left _ _
  have hδτ : C*δ ≤ τ := by
    have hh : δ ≤ τ/C := min_le_right _ _
    simpa only [mul_comm δ C] using (le_div_iff₀ hC).mp hh
  refine ⟨δ,hδ,?_⟩
  intro p hp f hf hU
  let q := radialPhase f
  have hdist : meanDistance f (fun x ↦ phase (q x)) ≤ δ := by
    rw [radialPhase_meanDistance f hf]
    linarith only [hU,uniformity_le_mean_norm n f hf]
  have hpert := uniformity_lipschitz n f (fun x ↦ phase (q x)) hf (fun x ↦ (phase_norm _).le)
  have hle := (le_abs_self (uniformityPower n f-uniformityPower n (fun x ↦ phase (q x)))).trans hpert
  have hmul := mul_le_mul_of_nonneg_left hdist (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n+1))
  have hqU : 1-τ ≤ uniformityPower n (fun x ↦ phase (q x)) := by
    dsimp only [C] at hδτ
    nlinarith only [hU,hle,hmul,hδτ]
  obtain ⟨r,hr,ha⟩ := hphase p hp q hqU
  refine ⟨r,hr,?_⟩
  have ht := meanDistance_triangle f (fun x ↦ phase (q x)) (fun x ↦ phase (r x))
  linarith only [ht,hdist,hδε,ha]

#print axioms near_maximal_cyclic_phase_inverse
#print axioms near_maximal_cyclic_inverse
end Erdos3NearMaximalCyclicInverse
