import Submission.WeightedFullRangeError
/-! Exact-type and axiom checks for weighted full-range errors. -/
open Nat Filter
open Erdos821.FullRangeError Erdos821.HigherDivisors Erdos821.AnalyticSieve

example (k : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ s : ℕ in atTop,
    c*(progressionScaleN s : ℝ)*(Real.log (progressionScaleN s))^k ≤
      divisorProgressionError (k+1) (progressionScaleN s) (progressionScaleN s) :=
  exists_weighted_full_error_log_lower k

example (k : ℕ) :
    ¬(fun s : ℕ => divisorProgressionError (k+1) (progressionScaleN s) (progressionScaleN s))
      =o[atTop] (fun s : ℕ => (progressionScaleN s : ℝ)*(Real.log (progressionScaleN s))^k) :=
  not_full_error_littleO_divisor_scale k

#print axioms weighted_main_minus_actual_le_error
#print axioms weighted_large_odd_progression_sum_le
#print axioms weighted_full_error_lower
#print axioms progressionScale_small_rpow
#print axioms exists_progression_divisor_weight_bound
#print axioms eventually_weighted_liftError_le
#print axioms odd_root_harmonic_lower
#print axioms exists_weighted_full_error_scale_lower
#print axioms exists_weighted_full_error_log_lower
#print axioms not_full_error_littleO_divisor_scale
