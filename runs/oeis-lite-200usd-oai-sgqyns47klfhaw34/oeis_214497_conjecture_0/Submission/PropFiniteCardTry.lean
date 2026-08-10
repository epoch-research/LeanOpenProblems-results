import FormalConjectures.Util.ProblemImports

#check Finite.of_subsingleton
#synth Finite Prop
#synth Fintype Prop
#synth Nontrivial Prop
#check Fintype.one_lt_card_iff_nontrivial
#check Fintype.card_eq_one_iff
#eval Fintype.card Prop

example : 1 < Fintype.card Prop := by
  exact (Fintype.one_lt_card_iff_nontrivial).2 inferInstance

example : Fintype.card Prop = 2 := by
  native_decide

example : False := by
  have hlt : 1 < Fintype.card Prop := (Fintype.one_lt_card_iff_nontrivial).2 inferInstance
  norm_num at hlt
