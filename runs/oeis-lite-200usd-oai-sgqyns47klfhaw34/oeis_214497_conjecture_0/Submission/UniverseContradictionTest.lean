import FormalConjectures.Util.ProblemImports

#synth Infinite (Type)
#synth Finite (Type)
#synth Nontrivial (Type)
#synth Subsingleton (Type)
#synth Infinite (Sort)
#synth Finite (Sort)
#synth Nontrivial (Sort)
#synth Subsingleton (Sort)
#synth Infinite (Prop)
#synth Finite (Prop)
#synth Nontrivial (Prop)
#synth Subsingleton (Prop)

example : False := by
  exact not_finite (Type)

example : False := by
  exact false_of_nontrivial_of_subsingleton (Type)
