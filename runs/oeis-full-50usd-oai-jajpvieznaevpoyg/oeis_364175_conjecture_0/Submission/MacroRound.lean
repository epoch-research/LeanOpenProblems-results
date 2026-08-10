import FormalConjectures.Util.ProblemImports
syntax "round" term : term
macro_rules | `(round $x) => `(0 : ℤ)
#check round (3:ℝ)
#eval ((round (3:ℝ)).toNat)
