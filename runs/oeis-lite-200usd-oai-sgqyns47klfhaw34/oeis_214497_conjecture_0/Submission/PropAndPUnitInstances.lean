import FormalConjectures.Util.ProblemImports
set_option synthInstance.maxHeartbeats 100000

#check PUnit.{0}
#check PUnit.{1}
#check PUnit.{2}
#synth Subsingleton PUnit.{1}
#synth Nontrivial PUnit.{1}
#synth Finite PUnit.{1}
#synth Infinite PUnit.{1}

#synth Nontrivial Prop
#synth Finite Prop
#synth Infinite Prop
#synth Subsingleton Prop
#synth Fintype Prop

example : False := by
  exact not_finite Prop

example : False := by
  exact false_of_nontrivial_of_subsingleton Prop
