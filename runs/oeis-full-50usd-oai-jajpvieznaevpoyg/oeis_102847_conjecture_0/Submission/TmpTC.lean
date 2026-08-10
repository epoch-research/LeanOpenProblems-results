import FormalConjectures.Util.ProblemImports

#synth Subsingleton PUnit
#synth Nontrivial PUnit
#synth Subsingleton Empty
#synth Nonempty Empty
example : False := by
  exact false_of_nontrivial_of_subsingleton PUnit
