import Submission.RecordLogBudget

/-! Exact-type and axiom checks for record logarithmic size accounting. -/
open Nat Filter
open scoped BigOperators
namespace Erdos821
example (s ε : ℝ) (hs : s < 1) (hε : 0 < ε) :
    ∀ᶠ P : ℕ in atTop, ∀ n : ℕ, 0 < n → 0 < gOddSquarefree n →
      (∀ j : ℕ, j ≤ n →
        (gOddSquarefree j : ℝ)/(j : ℝ)^s ≤ (gOddSquarefree n : ℝ)/(n : ℝ)^s) →
      (∀ m ∈ oddSquarefreeFiber n, ∀ p ∈ m.primeFactors, p ≤ P) →
      Real.log (n : ℝ) ≤ (P : ℝ)^(1-s+ε) :=
  eventually_record_log_le_input_cutoff_power s ε hs hε
#check @log_output_eq_sum_predecessor_logs
#print axioms log_output_eq_sum_predecessor_logs
#check @log_output_eq_sum_pool_predecessor_logs
#print axioms log_output_eq_sum_pool_predecessor_logs
#check @record_fiber_log_incidence
#print axioms record_fiber_log_incidence
#check @normalized_record_log_budget
#print axioms normalized_record_log_budget
#check @normalized_record_log_budget_pseries
#print axioms normalized_record_log_budget_pseries
#check @eventually_record_log_le_input_cutoff_power
#print axioms eventually_record_log_le_input_cutoff_power
#check @eventually_record_has_polylog_large_input_prime
#print axioms eventually_record_has_polylog_large_input_prime
end Erdos821
