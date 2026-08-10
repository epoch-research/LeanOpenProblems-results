import FormalConjectures.Util.ProblemImports
example (len : Nat) : (len + 2) / 2 < len + 2 := by
  exact Nat.div_lt_self (Nat.succ_pos _) (by norm_num)
example (len : Nat) : len + 2 - (len + 2)/2 < len + 2 := by
  have hpos : 0 < (len + 2) / 2 := Nat.div_pos (by omega) (by norm_num)
  exact Nat.sub_lt (by omega) hpos
