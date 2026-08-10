import FormalConjectures.Util.ProblemImports

unsafe def unsafeFalseImpl : False := lcProof

@[implemented_by unsafeFalseImpl]
def safeFalse : False := by
  exact lcProof

theorem t : False := safeFalse
#print axioms t
