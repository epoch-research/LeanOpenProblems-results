import Submission.TenThousandPoolStrictGain

/-! Expanded-type and axiom audits for the strict ten-thousand-band gain. -/

example : ∃ K : ℕ, 2 ≤ K ∧ ∀ γ : ℝ,
    γ < 2441371/4000002 + 1/(40000020*(K : ℝ)) →
    {n : ℕ | (({m : ℕ | Nat.totient m = n}.ncard : ℕ) : ℝ) >
      (n : ℝ)^γ}.Infinite :=
  Erdos821.exists_ten_thousand_pool_strict_gain

example :
    {n : ℕ | (({m : ℕ | Nat.totient m = n}.ncard : ℕ) : ℝ) >
      (n : ℝ)^(2441371/4000002 : ℝ)}.Infinite :=
  Erdos821.infinite_g_gt_ten_thousand_pool_endpoint

example : ∃ γ : ℝ, 2441371/4000002 < γ ∧
    {n : ℕ | (({m : ℕ | Nat.totient m = n}.ncard : ℕ) : ℝ) >
      (n : ℝ)^γ}.Infinite :=
  Erdos821.exists_exponent_above_ten_thousand_pool

example (ε : ℝ) (hε : 1558631/4000002 ≤ ε) :
    {n : ℕ | (({m : ℕ | Nat.totient m = n}.ncard : ℕ) : ℝ) >
      (n : ℝ)^(1-ε)}.Infinite :=
  Erdos821.erdos_821_ten_thousand_pool_closed_range ε hε

#print axioms Erdos821.exists_ten_thousand_pool_strict_gain
#print axioms Erdos821.infinite_g_gt_ten_thousand_pool_endpoint
#print axioms Erdos821.exists_exponent_above_ten_thousand_pool
#print axioms Erdos821.erdos_821_ten_thousand_pool_closed_range

#print axioms Erdos821.AnalyticSieve.tenThousandPool_band_parameters
#print axioms Erdos821.AnalyticSieve.tenThousandPool_budgetNat_sum
#print axioms Erdos821.ten_thousand_pool_threshold_improves_previous_strict_ceiling
