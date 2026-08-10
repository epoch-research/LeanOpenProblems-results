import FormalConjectures.Util.ProblemImports
open Finset Nat Int

example (n : ℕ) : ((n : ZMod n) = 0) := by simp
example (n : ℕ) (a : ℤ) : a ≡ 0 [ZMOD n] ↔ ((a : ZMod n) = 0) := by
  exact Int.modEq_zero_iff_dvd.trans ?_
