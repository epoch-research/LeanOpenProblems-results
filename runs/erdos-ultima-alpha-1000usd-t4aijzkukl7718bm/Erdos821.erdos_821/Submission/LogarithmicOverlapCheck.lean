import Submission.CompactPrimePool

/-! Exact-type checks and axiom audits for logarithmic pair overlap. -/

#print axioms Erdos821.LogarithmicOverlap.squarefree_log_totient_pool
#print axioms Erdos821.LogarithmicOverlap.fiber_incidence_identity
#print axioms Erdos821.LogarithmicOverlap.overlap_incidence_identity
#print axioms Erdos821.LogarithmicOverlap.fiber_log_square_le_pool_mul_overlap
#print axioms Erdos821.LogarithmicOverlap.overlap_le_large_pair_count
#print axioms Erdos821.LogarithmicOverlap.lower_large_pair_count
#print axioms Erdos821.LogarithmicOverlap.lower_large_pair_count_of_pool_bound
#print axioms Erdos821.LogarithmicOverlap.squarefree_family_card_le_pool_powerset
#print axioms Erdos821.LogarithmicOverlap.log_family_card_le_pool_weight
#print axioms Erdos821.LogarithmicOverlap.eventually_compact_pool_family_subpower
#print axioms Erdos821.LogarithmicOverlap.eventually_large_family_requires_large_pool
#print axioms Erdos821.LogarithmicOverlap.eventually_large_family_cauchy_coefficient_negative

open Erdos821.LogarithmicOverlap in
example (F P : Finset ℕ) (n : ℕ) (hn : 1 < n)
    (hP : ∀ p ∈ P, p.Prime)
    (hF : ∀ a ∈ F, Squarefree a ∧ Nat.totient a=n ∧ a.primeFactors ⊆ P)
    (η : ℝ) :
    (F.card : ℝ)^2*(Real.log (n : ℝ)-η*poolWeight P) ≤
      (1-η)*poolWeight P*((largePairs F n η).card : ℝ) :=
  lower_large_pair_count F P n hn hP hF η
