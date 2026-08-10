import FormalConjectures.Util.ProblemImports

open Nat

/--
A218585: Number of ways to write $n$ as $x+y$ with $0<x\le y$ and $x^2+xy+y^2$ prime.
-/
def A218585 (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n / 2)).sum fun x ↦
    let y := n - x
    if Nat.Prime (x * x + x * y + y * y) then 1 else 0

/-- Conjecture: a(n)>0 for all n>1 with the only exception n=8. -/
theorem oeis_218585_conjecture_0 :
  (∀ n : ℕ, 1 < n → n ≠ 8 → A218585 n > 0) ∧ (A218585 8 = 0) := by
  sorry
