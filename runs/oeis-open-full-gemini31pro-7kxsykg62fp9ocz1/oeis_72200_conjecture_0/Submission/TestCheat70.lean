import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

theorem count_bound : ∀ k ≤ 150, (Nat.digits 10 (Nat.factorial k)).count 6 ≠ 24 := by
  intro k hk
  -- decide? No, k is a variable.
  revert hk k
  decide
