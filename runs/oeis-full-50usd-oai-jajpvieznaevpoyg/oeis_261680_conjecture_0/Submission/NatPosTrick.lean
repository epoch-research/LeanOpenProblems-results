import FormalConjectures.Util.ProblemImports
example (m : Nat) : m > 0 := by
  change 0 < (m - 1) + 1
  exact Nat.succ_pos (m - 1)
