import FormalConjectures.Util.ProblemImports
#eval (decide ((0 : Int8) < Int8.minValue))
#eval (decide (Int8.minValue < (0 : Int8)))
example : ¬ ((0 : Int8) < Int8.minValue) := by decide
-- try contradictions from imported theorems
#check Int8.not_lt_minValue
#check Int16.not_lt_minValue
#check Int32.lt_irrefl
