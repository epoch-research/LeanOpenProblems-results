import FormalConjectures.Util.ProblemImports

open Nat

def holdsDec (n : ℕ) : Bool :=
  decide (∃ p ∈ Finset.range n, p.Prime ∧ (Nat.sqrt (n + p)).Prime)

def allHold (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => n ≤ 2 || holdsDec n

theorem test50 : allHold 50 = true := by native_decide
