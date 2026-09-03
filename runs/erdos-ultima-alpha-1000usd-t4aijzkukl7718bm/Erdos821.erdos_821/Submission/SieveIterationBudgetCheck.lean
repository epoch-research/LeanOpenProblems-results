import Submission.SieveIterationBudget

/-! Exact-type and axiom checks for the limitation of this particular sieve budget. -/
namespace Erdos821
#print axioms RetentionBudget.cofactor_le
#print axioms RetentionBudget.modulus_level_required
#print axioms RetentionBudget.cube_root_requires_large_modulus
#print axioms RetentionBudget.below_half_cutoff
#print axioms RetentionBudget.cube_root_not_below_half
#print axioms chebyshev_parameters_retention_budget
#print axioms chebyshev_parameters_cutoff_bound
#print axioms chebyshev_parameters_exponent_bound
#print axioms RetentionBudget.modulus_level_tends_to_one

example (r t b h : ℕ) (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b)
    (hc : (8320/675 : ℝ)*(t : ℝ)*h ≤ (27/32 : ℝ)*((b : ℝ)-1)^2) :
    1-(b : ℝ)/t < (5161/10000 : ℝ) :=
  chebyshev_parameters_exponent_bound r t b h heq hrt hb hc

example : (2064/4001 : ℚ) < 5161/10000 := by norm_num
example : (659/1000 : ℚ) < 105281/159744 := by norm_num
end Erdos821
