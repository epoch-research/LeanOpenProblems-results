import Submission.ProgressionLocalMode

/-! Exact-kernel and permitted-axiom audit for the surviving local mode. -/
open Nat Finset
open scoped BigOperators
open Erdos821.AnalyticSieve.SuccessorVaughan

example (L : ℕ) :
    (∑ r ∈ localModeSet L, ∑ t ∈ localModeSet L,
      (∑ s ∈ localModeSet L,
        successorKernel (successorProgressionWeight {3}) (successorProgressionPrincipal {3})
          ((3*L+1)^2) r s *
        successorKernel (successorProgressionWeight {3}) (successorProgressionPrincipal {3})
          ((3*L+1)^2) t s)^2) = (L : ℝ)^4/16 :=
  local_mode_gram_energy L

example (Q N : ℕ) :
    outputDivisorError (fun n => successorProgressionWeight {3} n-
      successorProgressionPrincipal {3} n) Q N ≤ (7/2 : ℝ)*Q :=
  local_mode_divisor_error Q N

#print axioms localModeSet_card
#print axioms localModeSet_properties
#print axioms singleton_three_baseline_difference
#print axioms local_mode_kernel
#print axioms local_mode_row_gram
#print axioms local_mode_gram_energy
#print axioms local_mode_divisor_error
#print axioms local_mode_gram_not_small
