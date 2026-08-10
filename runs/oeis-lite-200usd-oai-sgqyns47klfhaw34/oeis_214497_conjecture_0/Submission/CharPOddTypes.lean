import FormalConjectures.Util.ProblemImports

#synth Nontrivial Prop
#synth Add Prop
#synth Mul Prop
#synth Zero Prop
#synth One Prop
#synth NonAssocSemiring Prop
#synth CharP Prop 1
#synth CharP Prop 2

example : False := by
  exact CharP.false_of_nontrivial_of_char_one (R := Prop)

#print axioms this
