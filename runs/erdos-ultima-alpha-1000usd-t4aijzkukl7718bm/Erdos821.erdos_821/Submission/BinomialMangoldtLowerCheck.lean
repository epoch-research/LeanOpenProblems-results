import Submission.BinomialMangoldtLower

/-! Exact-type and axiom checks for the binomial Mangoldt lower bounds. -/

open Nat Filter ArithmeticFunction
open Erdos821.AnalyticSieve

example (N K : ℕ) (hN : 0 < N) :
    Real.log ((N.choose K : ℕ) : ℝ) ≤ mangoldtSum N :=
  log_choose_le_mangoldt N K hN
example : ∀ᶠ r : ℕ in atTop,
    (5/8 : ℝ) * ((2^r : ℕ) : ℝ) ≤ mangoldtSum (2^r) :=
  eventually_dyadic_mangoldt_five_eighths
#print axioms log_choose_le_mangoldt
#print axioms central_binomial_mangoldt_lower
#print axioms dyadic_binomial_mangoldt_lower
#print axioms eventually_dyadic_mangoldt_five_eighths
