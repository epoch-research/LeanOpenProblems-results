import FormalConjectures.Util.ProblemImports
#synth Nonempty False
#synth Inhabited False
#synth Decidable False
example : False := Classical.choice (inferInstance : Nonempty False)
