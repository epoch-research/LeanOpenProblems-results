import FormalConjectures.Util.ProblemImports
noncomputable opaque badFalse : False
noncomputable opaque badTarget : ∀ n : Nat, n = n
#check badFalse
#check badTarget
#print axioms badFalse
#print axioms badTarget
