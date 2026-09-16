import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

theorem count_sixes_test : (Nat.digits 10 (Nat.factorial 129)).count 6 = 23 := by
  decide
