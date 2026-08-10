import FormalConjectures.Util.ProblemImports
#synth Nonempty False
#synth ∀ p : Prop, Nonempty p
example (p : Prop) : p := Classical.choice (show Nonempty p from inferInstance)
