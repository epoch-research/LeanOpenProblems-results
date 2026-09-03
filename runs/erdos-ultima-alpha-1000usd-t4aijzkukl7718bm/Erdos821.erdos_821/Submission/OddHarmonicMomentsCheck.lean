import Submission.OddHarmonicMoments
/-! Exact-type and axiom checks for odd harmonic moments. -/
open Erdos821.HigherDivisors

example (k A : ℕ) (hA : 1 ≤ A) :
    (Real.log (A+1 : ℝ))^k/((2 : ℝ)^k*(k.factorial : ℝ)) ≤ oddHarmonicMoment k A :=
  oddHarmonicMoment_factorial_lower k A hA

#print axioms oddHarmonicMoment_nonneg
#print axioms hasSum_two_power_tau
#print axioms two_power_tau_sum_le
#print axioms harmonicMoment_le_two_pow_odd
#print axioms oddHarmonicMoment_factorial_lower
