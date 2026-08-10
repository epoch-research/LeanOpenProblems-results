import FormalConjectures.Util.ProblemImports
unsafe theorem unsafe_false : False := by
  exact unsafeCast True.intro
#print axioms unsafe_false
opaque opaque_false : False
theorem from_opaque : False := opaque_false
#print axioms from_opaque
axiom ax_false : False
theorem from_axiom : False := ax_false
#print axioms from_axiom
