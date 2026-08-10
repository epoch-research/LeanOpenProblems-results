import FormalConjectures.Util.ProblemImports
open scoped Nat.Prime
example : π 20 = 8 := by norm_num [Nat.primeCounting]
example : (π (π (4*5))).sqrt ^ 2 = π (π (4*5)) := by norm_num [Nat.primeCounting]
