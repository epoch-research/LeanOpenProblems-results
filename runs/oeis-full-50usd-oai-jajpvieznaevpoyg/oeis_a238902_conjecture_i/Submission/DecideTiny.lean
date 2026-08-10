import FormalConjectures.Util.ProblemImports
open scoped Nat.Prime
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

example : a 1 > 0 := by decide
example : a 2 > 0 := by decide
example : a 5 > 0 := by decide
--example : a 10 > 0 := by decide
