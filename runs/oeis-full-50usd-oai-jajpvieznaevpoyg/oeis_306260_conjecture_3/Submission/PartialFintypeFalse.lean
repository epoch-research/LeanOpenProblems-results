import FormalConjectures.Util.ProblemImports
partial def badFintype (_ : Unit) : Fintype ℕ := badFintype ()
local instance : Fintype ℕ := badFintype ()
theorem false_bad : False := Fintype.false (α := ℕ) inferInstance
#print axioms false_bad
#print opaques false_bad
