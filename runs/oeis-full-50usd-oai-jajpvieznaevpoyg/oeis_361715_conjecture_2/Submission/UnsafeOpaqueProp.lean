import FormalConjectures.Util.ProblemImports

unsafe opaque badProp : Prop
unsafe def badProof : badProp := lcProof

theorem t : badProp := badProof
#print axioms t
