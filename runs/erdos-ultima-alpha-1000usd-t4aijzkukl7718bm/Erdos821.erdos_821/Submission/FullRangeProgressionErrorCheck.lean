import Submission.FullRangeProgressionError
/-! Exact-type and axiom audit of the full-range absolute-error bound. -/

open Nat Filter
open Erdos821.FullRangeError Erdos821.AnalyticSieve Erdos821.HigherDivisors

example (N : ℕ) (hN : 0 < N) :
    mangoldtSum (4*N)/4 - characterLiftError 2 (4*N) ≤
      divisorProgressionError 1 (4*N) (4*N) := full_error_lower N hN

example : ∀ᶠ L : ℕ in atTop, ∀ k : ℕ, 1 ≤ k →
    mangoldtSum (2^(L+2))/8 ≤ divisorProgressionError k (2^(L+2)) (2^(L+2)) :=
  eventually_full_error_ge_psi

example : ∀ᶠ L : ℕ in atTop, ∀ k : ℕ, 1 ≤ k →
    ((2^(L+2) : ℕ) : ℝ)/((L : ℝ)+1)^2 <
      divisorProgressionError k (2^(L+2)) (2^(L+2)) :=
  eventually_full_error_gt_log_square

#print axioms residueOneMangoldt_large_modulus
#print axioms large_odd_progression_sum_le
#print axioms error_one_eq
#print axioms main_minus_actual_le_error
#print axioms oddLargeModuli_card
#print axioms oddLargeModuli_properties
#print axioms full_error_lower
#print axioms error_one_le_higher
#print axioms full_error_dyadic_lower
#print axioms eventually_full_error_ge_psi
#print axioms eventually_full_error_ge_dyadic_scale
#print axioms eventually_full_error_gt_log_square

example : ∀ᶠ s : ℕ in atTop, ∀ k : ℕ, 1 ≤ k →
    (progressionScaleN s : ℝ)/64 ≤
      divisorProgressionError k (progressionScaleN s) (progressionScaleN s) :=
  eventually_full_error_ge_linear

#print axioms eventually_full_error_ge_linear
