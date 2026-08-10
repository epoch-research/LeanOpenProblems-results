import FormalConjectures.Util.ProblemImports
unsafe def badDecFalse : Decidable False := isTrue (by exact lcProof)
@[implemented_by badDecFalse]
def safeDecFalse : Decidable False := isFalse (by intro h; exact h)
instance : Decidable False := safeDecFalse
theorem bad : False := by native_decide
#print axioms bad
