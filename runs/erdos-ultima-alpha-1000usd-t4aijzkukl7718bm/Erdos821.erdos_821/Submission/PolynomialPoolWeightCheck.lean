import Submission.PolynomialPoolWeightApplications

/-! Exact-type and axiom checks for polynomial logarithmic pool weights. -/

#print axioms Erdos821.LogarithmicOverlap.finite_fiber_weight_le_pool_product
#print axioms Erdos821.LogarithmicOverlap.log_finite_fiber_le_pool_sum
#print axioms Erdos821.LogarithmicOverlap.finite_rpow_sum_le_card_power
#print axioms Erdos821.LogarithmicOverlap.poolRankinConstant_pos
#print axioms Erdos821.LogarithmicOverlap.prime_pool_sum_le_weight_power
#print axioms Erdos821.LogarithmicOverlap.log_finite_fiber_le_pool_weight_power
#print axioms Erdos821.LogarithmicOverlap.eventually_pool_weight_bound_controls_fiber
#print axioms Erdos821.LogarithmicOverlap.exists_pool_rankin_parameters
#print axioms Erdos821.LogarithmicOverlap.eventually_large_fiber_requires_polynomial_pool
#print axioms Erdos821.CoprimeRecords.exists_large_fiber_with_polynomial_pool_bound
#print axioms Erdos821.CoprimeRecords.exists_large_fiber_with_superquadratic_pool_bound

open Filter Erdos821.LogarithmicOverlap in
example (C α β : ℝ) (hC : 0 ≤ C) (hα : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hβα : β*(1-α) < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ F P : Finset ℕ,
      (∀ p ∈ P, Nat.Prime p) →
      (∀ a ∈ F, Nat.totient a=n ∧ a.primeFactors ⊆ P) →
      (n : ℝ)^α < (F.card : ℝ) →
      C*(Real.log (n : ℝ))^β < ∑ p ∈ P, Real.log ((p-1 : ℕ) : ℝ) := by
  exact eventually_large_fiber_requires_polynomial_pool C α β hC hα hα1 hβ hβα
