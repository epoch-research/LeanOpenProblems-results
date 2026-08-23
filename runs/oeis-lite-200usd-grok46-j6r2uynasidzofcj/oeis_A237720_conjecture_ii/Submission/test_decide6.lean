import FormalConjectures.Util.ProblemImports

open Nat

def holdsDec (n : ℕ) : Bool :=
  decide (∃ p ∈ Finset.range n, p.Prime ∧ (Nat.sqrt (n + p)).Prime)

theorem allHold_5000 : ∀ n ≤ 5000, n ≤ 2 ∨ holdsDec n = true := by native_decide
