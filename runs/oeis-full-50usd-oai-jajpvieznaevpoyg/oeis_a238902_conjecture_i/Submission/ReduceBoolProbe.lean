import FormalConjectures.Util.ProblemImports
#reduce Lean.reduceBool false
#reduce Lean.reduceBool true
example : false = true := Lean.ofReduceBool false true (by native_decide)
#print axioms ReduceBoolProbe._example_1
