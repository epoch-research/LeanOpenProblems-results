import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000
theorem test : Nat.totient 100000 = 40000 := by decide
