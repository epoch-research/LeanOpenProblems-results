import FormalConjectures.Util.ProblemImports

open Nat Real Finset
open scoped Chebyshev

/-!
Elementary Chebyshev lower bound: `θ x ≥ (log 2 / 2) * x` for large `x`.
Follows the standard central-binomial argument.
-/

lemma log_centralBinom_eq_sum (n : ℕ) :
    log (centralBinom n : ℝ) =
      ∑ p ∈ range (2 * n + 1) with p.Prime,
        ((centralBinom n).factorization p : ℝ) * log p := by
  sorry

-- We'll fill this in properly.
