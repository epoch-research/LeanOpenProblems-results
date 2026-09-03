import Submission.ThousandPoolMultiplicity

/-! Type and axiom audits for the certified thousand-band multiplicity bound. -/

open Nat Filter
open scoped BigOperators

#check Erdos821.AnalyticSieve.poolBandLimit_le_rational
#check Erdos821.AnalyticSieve.poolBandLimit_lt_certificate
#check Erdos821.AnalyticSieve.thousandPool_band_parameters
#check Erdos821.AnalyticSieve.thousandPool_budgetNat_sum
#check Erdos821.AnalyticSieve.eventually_thousand_pool_rough_rejection_bound
#check Erdos821.exists_thousand_pool_smooth_prime_count
#check Erdos821.infinite_g_gt_thousand_pool_gain

example (γ : ℝ) (hγ : γ < 406887/666667) :
    {n : ℕ | (({m : ℕ | Nat.totient m = n}.ncard : ℕ) : ℝ) >
      (n : ℝ)^γ}.Infinite :=
  Erdos821.infinite_g_gt_thousand_pool_gain γ hγ

example :
    {n : ℕ | (({m : ℕ | Nat.totient m = n}.ncard : ℕ) : ℝ) >
      (n : ℝ)^(61033/100000 : ℝ)}.Infinite :=
  Erdos821.infinite_g_gt_thousand_band_decimal

example (ε : ℝ) (hε : 259780/666667 < ε) :
    {n : ℕ | (({m : ℕ | Nat.totient m = n}.ncard : ℕ) : ℝ) >
      (n : ℝ)^(1-ε)}.Infinite :=
  Erdos821.erdos_821_thousand_pool_range ε hε
#print axioms Erdos821.AnalyticSieve.poolBandNumerator
#print axioms Erdos821.AnalyticSieve.poolBandDenominator
#print axioms Erdos821.AnalyticSieve.poolBandDenominator_pos
#print axioms Erdos821.AnalyticSieve.poolBandLimit_le_rational
#print axioms Erdos821.AnalyticSieve.poolBandCertificate
#print axioms Erdos821.AnalyticSieve.poolBandLimit_lt_certificate
#print axioms Erdos821.AnalyticSieve.thousandPoolEndpoint
#print axioms Erdos821.AnalyticSieve.thousandPoolB
#print axioms Erdos821.AnalyticSieve.thousandPoolL
#print axioms Erdos821.AnalyticSieve.thousandPoolBudgetNat
#print axioms Erdos821.AnalyticSieve.thousandPoolBudget
#print axioms Erdos821.AnalyticSieve.thousandPool_band_parameters
#print axioms Erdos821.AnalyticSieve.thousandPool_band_limit
#print axioms Erdos821.AnalyticSieve.thousandPool_budgetNat_sum
#print axioms Erdos821.AnalyticSieve.thousandPool_budget_sum
#print axioms Erdos821.AnalyticSieve.eventually_all_thousand_pool_bands
#print axioms Erdos821.AnalyticSieve.hyperbolic_card_le_thousand_pool_bands
#print axioms Erdos821.AnalyticSieve.eventually_thousand_pool_rough_rejection_bound
#print axioms Erdos821.exists_thousand_pool_smooth_prime_count_enlarged
#print axioms Erdos821.exists_thousand_pool_smooth_prime_count
#print axioms Erdos821.infinite_g_gt_thousand_pool_gain
#print axioms Erdos821.infinite_g_gt_thousand_band_decimal
#print axioms Erdos821.erdos_821_thousand_pool_range
#print axioms Erdos821.thousand_pool_threshold_improves_fine_pool
