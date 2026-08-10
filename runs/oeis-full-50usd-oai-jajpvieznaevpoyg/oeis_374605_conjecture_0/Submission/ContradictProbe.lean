import FormalConjectures.Util.ProblemImports
#check false_of_nontrivial_of_subsingleton
example : False := by
  exact false_of_nontrivial_of_subsingleton (ZMod 1)
example : False := by
  exact false_of_nontrivial_of_subsingleton (ULift PUnit)
example : False := by
  exact false_of_nontrivial_of_subsingleton (Fin 1)
