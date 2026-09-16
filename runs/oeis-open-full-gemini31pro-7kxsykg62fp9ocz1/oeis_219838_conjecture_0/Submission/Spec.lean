import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  (Icc 1 (n / 2)).sum fun x : ℕ =>
    let xy_prod := x * (n - x)
    if Nat.Prime (xy_prod ^ 2 + xy_prod + 1) then 1 else 0

theorem oeis_219838_conjecture_0 : ∀ (n : ℕ), n > 1 → a n > 0 := by
  sorry

theorem oeis_219838_conjecture_0.disproof : ¬ (∀ (n : ℕ), n > 1 → a n > 0) := by
  sorry
