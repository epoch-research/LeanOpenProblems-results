import FormalConjectures.Util.ProblemImports
example (m : Nat) : m > 0 := by
  have h : 0 < (m - 1) + 1 := Nat.succ_pos (m - 1)
  omega
