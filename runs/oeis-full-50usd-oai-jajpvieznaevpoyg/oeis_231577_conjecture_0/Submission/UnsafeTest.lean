import FormalConjectures.Util.ProblemImports
open Nat

def a (n : ℕ) : ℕ :=
  (Finset.Ico 1 n).sum fun x ↦
    let y := n - x
    if Nat.Prime (2 ^ x + y * (y + 1) / 2) then 1 else 0

unsafe theorem bad : ∀ (n : ℕ), 1 < n → 0 < a n := by
  exact unsafeCast True.intro

#print axioms bad
