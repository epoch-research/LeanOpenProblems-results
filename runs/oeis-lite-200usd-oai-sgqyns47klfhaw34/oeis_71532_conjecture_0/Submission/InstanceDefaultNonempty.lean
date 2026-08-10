import FormalConjectures.Util.ProblemImports
axiom P : Prop

-- Instance whose field is just a parameter; see if synth can use default/self.
noncomputable instance instNEP (h : Nonempty P := by infer_instance) : Nonempty P := h

#synth Nonempty P
example : P := Classical.choice (inferInstance : Nonempty P)
#print axioms instNEP
#print axioms _example
