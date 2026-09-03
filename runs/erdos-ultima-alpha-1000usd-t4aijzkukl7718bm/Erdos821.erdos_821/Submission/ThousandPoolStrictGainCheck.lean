import Submission.ThousandPoolStrictGain

/-! Expanded-type and axiom audits for the strict thousand-band gain. -/

example : ∃ K : ℕ, 2 ≤ K ∧ ∀ γ : ℝ,
    γ < 406887/666667 + 1/(40000020*(K : ℝ)) →
    {n : ℕ | (({m : ℕ | Nat.totient m = n}.ncard : ℕ) : ℝ) >
      (n : ℝ)^γ}.Infinite :=
  Erdos821.exists_thousand_pool_strict_gain

example :
    {n : ℕ | (({m : ℕ | Nat.totient m = n}.ncard : ℕ) : ℝ) >
      (n : ℝ)^(406887/666667 : ℝ)}.Infinite :=
  Erdos821.infinite_g_gt_thousand_pool_endpoint

example : ∃ γ : ℝ, 406887/666667 < γ ∧
    {n : ℕ | (({m : ℕ | Nat.totient m = n}.ncard : ℕ) : ℝ) >
      (n : ℝ)^γ}.Infinite :=
  Erdos821.exists_exponent_above_thousand_pool

example (ε : ℝ) (hε : 259780/666667 ≤ ε) :
    {n : ℕ | (({m : ℕ | Nat.totient m = n}.ncard : ℕ) : ℝ) >
      (n : ℝ)^(1-ε)}.Infinite :=
  Erdos821.erdos_821_thousand_pool_closed_range ε hε

#print axioms Erdos821.exists_thousand_pool_strict_gain
#print axioms Erdos821.infinite_g_gt_thousand_pool_endpoint
#print axioms Erdos821.exists_exponent_above_thousand_pool
#print axioms Erdos821.erdos_821_thousand_pool_closed_range
