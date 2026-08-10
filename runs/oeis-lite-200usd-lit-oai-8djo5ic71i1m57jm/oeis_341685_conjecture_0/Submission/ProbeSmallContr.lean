import FormalConjectures.Util.ProblemImports
#check not_small_type
#check not_small_cardinal
#check Small
#synth Small.{0,1} (Type 0)
#synth Small.{0,2} (Type 1)
#synth Small.{1,2} (Type 1)
#synth Small.{0,1} Cardinal

example : False := by
  exact not_small_type (inferInstance)
