import FormalConjectures.Util.ProblemImports
open Nat Finset
def a (n : ℕ) : ℕ := card ((Icc 1 n).filter fun k : ℕ => Nat.Prime (k ^ 4 + (2 * n + 1 - k) ^ 4))
theorem test100 : a 100 > 0 := by native_decide
