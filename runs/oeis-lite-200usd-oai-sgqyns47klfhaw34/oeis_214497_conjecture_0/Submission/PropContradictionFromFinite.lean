import FormalConjectures.Util.ProblemImports
#check Equiv.propEquivBool
#check not_subsingleton
#check not_subsingleton Prop
#check not_subsingleton Bool
#check Fintype.card_ne_one_iff
#check Fintype.one_lt_card_iff_nontrivial
#check Fintype.card_eq_one_iff
#check fintype_card_eq_zero_iff

example : Nontrivial Prop := inferInstance
example : Finite Prop := inferInstance
example : Fintype Prop := inferInstance
example : ¬ Subsingleton Prop := not_subsingleton Prop

example : False := by
  have hfin : Finite Prop := inferInstance
  have hnt : Nontrivial Prop := inferInstance
  exact?
