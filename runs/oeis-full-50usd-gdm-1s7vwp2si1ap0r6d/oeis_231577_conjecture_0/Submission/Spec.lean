import FormalConjectures.Util.ProblemImports

open Nat

/--
A231577: Number of ways to write $n = x + y$ ($x, y > 0$) with $2^x + y(y+1)/2$ prime.
-/
def a (n : ℕ) : ℕ :=
  (Finset.Ico 1 n).sum fun x ↦
    let y := n - x
    -- 1 ≤ x < n ensures $x$ and $y$ are positive.
    if Nat.Prime (2 ^ x + y * (y + 1) / 2) then 1 else 0


#eval a 2
#eval a 3
#eval a 4
#eval a 5
#eval a 6

/-- Conjecture: a(n) > 0 for all n > 1. -/
theorem oeis_231577_conjecture_0 : ∀ (n : ℕ), 1 < n → 0 < a n := by
  sorry
