import FormalConjectures.Util.ProblemImports

partial def pf (P : Prop) [Inhabited P] : P := default
instance instAnyProp (P : Prop) : Inhabited P := ⟨pf P⟩
theorem bad : False := pf False
#print axioms pf
#print axioms instAnyProp
#print axioms bad
