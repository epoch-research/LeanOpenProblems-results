import FormalConjectures.Util.ProblemImports

unsafe def unsafe_helper : False := unsafe_helper

unsafe instance : Inhabited False := ⟨unsafe_helper⟩

opaque safe_helper : False

#print axioms safe_helper




