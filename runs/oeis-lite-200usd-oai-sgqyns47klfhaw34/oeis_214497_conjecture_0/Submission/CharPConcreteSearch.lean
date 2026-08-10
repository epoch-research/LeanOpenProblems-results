import FormalConjectures.Util.ProblemImports

example : False := by
  exact @CharP.false_of_nontrivial_of_char_one PUnit _ _ _

example : False := by
  exact @CharP.false_of_nontrivial_of_char_one Bool _ _ _

example : False := by
  exact @CharP.false_of_nontrivial_of_char_one Prop _ _ _

example : False := by
  exact @CharP.false_of_nontrivial_of_char_one (ULift PUnit) _ _ _
