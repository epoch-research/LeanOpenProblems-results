import FormalConjectures.Util.ProblemImports
-- Check whether decide (not native) for small false prop adds trustCompiler or is impossible.
theorem smallEq : (1:ℕ) = 1 := by decide
#print axioms smallEq
-- theorem impossible : False := by decide
