import Submission.ThousandPoolClosedFibers

/-! Expanded types and axiom audit for the closed-output specialization. -/
open scoped BigOperators

example : ∃ K : ℕ, 2 ≤ K ∧ ∀ γ : ℝ, 0 ≤ γ →
    γ < 406887/666667+1/(40000020*(K : ℝ)) → ∀ r N : ℕ,
    ∃ n : ℕ, N < n ∧
      (n : ℝ)^γ < (({m : ℕ | Nat.totient m = n}.ncard : ℕ) : ℝ) ∧
      (∏ p ∈ n.primeFactors, p)^r ≤ n ∧
      Nat.totient (∏ p ∈ n.primeFactors, p) ∣ n :=
  Erdos821.ClosedPadding.exists_thousand_pool_closed_strict_gain

example (r : ℕ) :
    {n : ℕ | (n : ℝ)^(406887/666667 : ℝ) <
        (({m : ℕ | Nat.totient m = n}.ncard : ℕ) : ℝ) ∧
      (∏ p ∈ n.primeFactors, p)^r ≤ n ∧
      Nat.totient (∏ p ∈ n.primeFactors, p) ∣ n}.Infinite :=
  Erdos821.ClosedPadding.infinite_thousand_pool_closed_endpoint r

example : ∃ γ : ℝ, 406887/666667 < γ ∧ ∀ r : ℕ,
    {n : ℕ | (n : ℝ)^γ < (({m : ℕ | Nat.totient m = n}.ncard : ℕ) : ℝ) ∧
      (∏ p ∈ n.primeFactors, p)^r ≤ n ∧
      Nat.totient (∏ p ∈ n.primeFactors, p) ∣ n}.Infinite :=
  Erdos821.ClosedPadding.exists_closed_exponent_above_thousand_pool

#print axioms Erdos821.ClosedPadding.closed_fibers_of_single_log_smooth_count
#print axioms Erdos821.ClosedPadding.exists_thousand_pool_closed_strict_gain
#print axioms Erdos821.ClosedPadding.infinite_thousand_pool_closed_endpoint
#print axioms Erdos821.ClosedPadding.exists_closed_exponent_above_thousand_pool
