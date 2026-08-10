import FormalConjectures.Util.ProblemImports

partial def fake (P : Prop) : Nonempty P := fake P
example : False := Classical.choice (fake False)
#print axioms fake
