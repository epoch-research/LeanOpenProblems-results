import FormalConjectures.Util.ProblemImports
#synth Semiring Prop
#synth Nontrivial Prop
#synth CharP Prop 1
#synth CharP Prop 2
example : False := by
  exact CharP.false_of_nontrivial_of_char_one (R := Prop)
