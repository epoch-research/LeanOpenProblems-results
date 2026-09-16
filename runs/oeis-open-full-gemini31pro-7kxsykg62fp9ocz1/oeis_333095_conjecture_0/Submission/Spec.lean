import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else
    ((Finset.sum (range (n + 1)) fun k =>
      let N := 3 * n
      let term_val : ℚ := (N : ℚ) / (N + 2 * k : ℚ) * ((N + 2 * k).choose k : ℚ)
      term_val
    ).floor).toNat

theorem oeis_333095_conjecture_0 (p n k : ℕ) :
  p.Prime → 5 ≤ p → 0 < n → 0 < k →
  a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] := by
  sorry

theorem oeis_333095_conjecture_0.disproof : ¬ (type_of% @oeis_333095_conjecture_0) := sorry
