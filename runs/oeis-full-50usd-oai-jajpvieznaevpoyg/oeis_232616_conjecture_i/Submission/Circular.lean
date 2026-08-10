import FormalConjectures.Util.ProblemImports

instance badNonempty : Nonempty False := ⟨Classical.choice badNonempty⟩
example : False := Classical.choice badNonempty
#print axioms badNonempty
