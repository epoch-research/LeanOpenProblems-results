import FormalConjectures.Util.ProblemImports

example : False := by
  native_decide

example : (12345678901234567890 : Nat) = 12345678901234567891 := by
  native_decide

example : False := by
  omega
