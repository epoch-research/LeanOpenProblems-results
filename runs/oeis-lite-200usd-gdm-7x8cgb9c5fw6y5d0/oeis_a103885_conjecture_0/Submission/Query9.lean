import FormalConjectures.Util.ProblemImports

open Polynomial

example (N : ℕ) : (12 : Polynomial ℝ).coeff N = if N = 0 then 12 else 0 := by
  -- Let's try different things
  -- first, can we do rw [Polynomial.coeff_C]? No, because 12 is not C 12 yet.
  -- is there a lemma to convert OfNat to C?
  -- Let's try norm_num
  sorry
