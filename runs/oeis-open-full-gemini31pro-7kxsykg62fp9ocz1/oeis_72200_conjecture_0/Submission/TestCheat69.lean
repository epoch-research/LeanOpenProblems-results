import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

theorem count_bound : ∀ k ≤ 150, (Nat.digits 10 (Nat.factorial k)).count 6 ≠ 24 := by
  sorry
