import FormalConjectures.Util.ProblemImports

#synth Fintype Prop
#synth Finite Prop
#synth Infinite Prop

example : Infinite Prop := by
  -- likely impossible due propext collapsing Prop to two values
  infer_instance

example : False := by
  exact not_finite Prop
