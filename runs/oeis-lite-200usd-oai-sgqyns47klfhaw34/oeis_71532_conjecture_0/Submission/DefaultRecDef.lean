import FormalConjectures.Util.ProblemImports
axiom P : Prop

noncomputable def proofDef (h : P := proofDef) : P := h
#print proofDef
#print axioms proofDef
example : P := proofDef
#print axioms _example

noncomputable def neDef (h : Nonempty P := ⟨neDef⟩) : Nonempty P := h
example : P := Classical.choice neDef
#print axioms neDef
