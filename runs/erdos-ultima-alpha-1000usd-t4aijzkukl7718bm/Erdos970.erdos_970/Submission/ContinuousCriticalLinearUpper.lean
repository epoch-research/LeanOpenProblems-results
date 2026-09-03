import Submission.ContinuousCriticalKernelUpper

/-! Linear-in-depth upper bounds for the continuous critical positive-cost
iteration. The outer maximum is kept exactly; no arithmetic transfer or
quadratic Jacobsthal bound is claimed. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology ENNReal
set_option maxHeartbeats 1800000

lemma criticalCostIteration_le_succ (S B : ℝ → ℝ≥0∞) (n : ℕ) (s : ℝ) :
    criticalCostIteration S B n s ≤ criticalCostIteration S B (n+1) s :=
  le_max_left _ _

/-- Positivity of the kernel makes the increasing-envelope recurrence equal
to an iteration with the fixed initial obstacle. The previous iterate is not
charged as an additional source at every step. -/
theorem criticalCostIteration_fixed_obstacle (S B : ℝ → ℝ≥0∞) (n : ℕ) (s : ℝ) :
    criticalCostIteration S B (n+1) s =
      max (B s) (S s+criticalCostKernel (criticalCostIteration S B n) s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hk := criticalCostKernel_mono
      (fun v _ => criticalCostIteration_le_succ S B n v) s
    change max (criticalCostIteration S B (n+1) s)
      (S s+criticalCostKernel (criticalCostIteration S B (n+1)) s) = _
    rw [ih, max_assoc, max_eq_right (add_le_add le_rfl hk)]

/-- The invariant mass and fixed-obstacle form give a linear upper bound.
This holds for extended-valued masses as well as finite ones. -/
theorem criticalCostIteration_mass_upper (S B : ℝ → ℝ≥0∞)
    (hS : Measurable S) (hB : Measurable B) (n : ℕ) :
    criticalMass (criticalCostIteration S B n) ≤
      ((n : ℝ≥0∞)+1)*criticalMass B+(n : ℝ≥0∞)*criticalMass S := by
  induction n with
  | zero => simp [criticalCostIteration]
  | succ n ih =>
    have hm := criticalMass_mono (F := criticalCostIteration S B (n+1))
      (G := fun s => B s+(S s+criticalCostKernel (criticalCostIteration S B n) s))
      (fun s _ => by
        rw [criticalCostIteration_fixed_obstacle]
        exact max_le_add_of_nonneg (zero_le _) (zero_le _))
    rw [criticalMass_add _ _ hB, criticalMass_add _ _ hS,
      criticalMass_invariant _ (criticalCostIteration_measurable S B hS hB n)] at hm
    have hh := hm.trans (add_le_add le_rfl (add_le_add le_rfl ih))
    convert hh using 1
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    ring

/-- Pointwise linear growth at every real level, with the initial obstacle
and source still displayed. No source cost has been dropped. -/
theorem criticalCostIteration_pointwise_upper (S B : ℝ → ℝ≥0∞)
    (hS : Measurable S) (hB : Measurable B) (n : ℕ) (s : ℝ) :
    criticalCostIteration S B (n+1) s ≤ max (B s)
      (S s+ENNReal.ofReal (criticalCoefficient (max 2 (s-1))) *
        (((n : ℝ≥0∞)+1)*criticalMass B+(n : ℝ≥0∞)*criticalMass S)) := by
  rw [criticalCostIteration_fixed_obstacle]
  apply max_le_max le_rfl
  apply add_le_add le_rfl
  exact (criticalCostKernel_le_coefficient_mass _
    (criticalCostIteration_measurable S B hS hB n) s).trans
    (mul_le_mul_right (criticalCostIteration_mass_upper S B hS hB n) _)

/-- A level-independent pointwise upper estimate. -/
theorem criticalCostIteration_pointwise_upper_uniform (S B : ℝ → ℝ≥0∞)
    (hS : Measurable S) (hB : Measurable B) (n : ℕ) (s : ℝ) :
    criticalCostIteration S B (n+1) s ≤ max (B s)
      (S s+(3/4 : ℝ≥0∞)*
        (((n : ℝ≥0∞)+1)*criticalMass B+(n : ℝ≥0∞)*criticalMass S)) := by
  rw [criticalCostIteration_fixed_obstacle]
  apply max_le_max le_rfl
  apply add_le_add le_rfl
  exact (criticalCostKernel_le_three_fourths_mass _
    (criticalCostIteration_measurable S B hS hB n) s).trans
    (mul_le_mul_right (criticalCostIteration_mass_upper S B hS hB n) _)

/-- Finite-mass finite-valued initial data stay finite at every finite depth,
even though the positive-source model diverges as depth tends to infinity. -/
theorem criticalCostIteration_finite (S B : ℝ → ℝ≥0∞)
    (hS : Measurable S) (hB : Measurable B)
    (hMS : criticalMass S ≠ ⊤) (hMB : criticalMass B ≠ ⊤)
    (n : ℕ) (s : ℝ) (hSs : S s ≠ ⊤) (hBs : B s ≠ ⊤) :
    criticalCostIteration S B n s ≠ ⊤ := by
  cases n with
  | zero => exact hBs
  | succ n =>
    apply ne_top_of_le_ne_top _ (criticalCostIteration_pointwise_upper_uniform S B hS hB n s)
    finiteness

/-- The compact potential has matching linear upper and lower bounds at two.
This describes only the continuous positive-cost model. -/
theorem criticalCompactPotential_two_linear (n : ℕ) :
    (n : ℝ≥0∞)/44 ≤ criticalCompactPotential (n+1) 2 ∧
      criticalCompactPotential (n+1) 2 ≤ (3/8 : ℝ≥0∞)*n :=
  ⟨criticalCompactPotential_two_growth n, criticalCompactPotential_two_upper n⟩

#print axioms criticalCostIteration_fixed_obstacle
#print axioms criticalCostIteration_mass_upper
#print axioms criticalCostIteration_pointwise_upper
#print axioms criticalCostIteration_pointwise_upper_uniform
#print axioms criticalCostIteration_finite
#print axioms criticalCompactPotential_two_linear
end Erdos970.ContinuousBuchstab
