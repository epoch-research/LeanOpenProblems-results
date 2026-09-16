import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

theorem count_sixes_test : ∃ k, (Nat.digits 10 (Nat.factorial k)).count 6 = 23 := by
  use 129
  rfl
