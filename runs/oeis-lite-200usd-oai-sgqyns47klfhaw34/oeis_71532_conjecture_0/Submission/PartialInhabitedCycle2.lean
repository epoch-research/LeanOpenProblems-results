import FormalConjectures.Util.ProblemImports

partial def cycInhabited (P : Prop) : Inhabited P := ⟨default⟩
attribute [local instance] cycInhabited
example : False := default
#print axioms cycInhabited
#print axioms _example
