import FormalConjectures.Util.ProblemImports
structure Wrap (P : Prop) where
  pr : P
  deriving Nonempty
#synth Nonempty (Wrap False)
theorem bad : False := (Classical.choice (show Nonempty (Wrap False) from inferInstance)).pr
#print axioms bad
