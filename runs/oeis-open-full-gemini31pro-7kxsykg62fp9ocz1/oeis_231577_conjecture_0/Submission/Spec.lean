import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  (Finset.Ico 1 n).sum fun x ↦
    let y := n - x
    if Nat.Prime (2 ^ x + y * (y + 1) / 2) then 1 else 0

theorem oeis_231577_conjecture_0 : ∀ (n : ℕ), 1 < n → 0 < a n := by
  sorry

theorem oeis_231577_conjecture_0.disproof : ¬ (type_of% @oeis_231577_conjecture_0) := sorry
