import FormalConjectures.Util.ProblemImports

-- verify suspect custom statements on edge cases, trying to derive False if false
example : Nat.IsPerfectPower 16 := by decide +native
example : ¬ Nat.IsPerfectPower 12 := by decide +native
example : Nat.squarefreePart 0 = 1 := by simp
example : Nat.squarefreePart 1 = 1 := by native_decide
example : Nat.squarefreePart 4 = 1 := by native_decide
example : (0:ℕ).Full 5 := Nat.Full.zero_left 5
example : (5:ℕ).Full 0 := Nat.Full.zero_right 5
example : Nat.maxPrimeFac 0 = 0 := by simp
example : Nat.maxPrimeFac 1 = 0 := by simp
example : Nat.maxPrimeFac 12 = 3 := by native_decide
