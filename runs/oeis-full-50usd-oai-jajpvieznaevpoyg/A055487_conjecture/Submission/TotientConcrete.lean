import FormalConjectures.Util.ProblemImports
example : ¬ Nat.totient 3 = Nat.factorial 4 := by decide
example (h : Nat.totient 3 = Nat.factorial 4) : False := by
  exact (by decide : ¬ Nat.totient 3 = Nat.factorial 4) h
