import FormalConjectures.Util.ProblemImports

#check Function.cantor_surjective
#check Function.not_surjective_setOf
#check Cantor
#check Cardinal.cantor
#check Cardinal.cantor' 
#check Cardinal.mk_set
#check Cardinal.mk_univ
#check Fintype.card_fun
#check Fintype.card_prop

example : False := by
  -- Try deriving contradiction from identity/surjection Prop -> Set Prop
  have hcant := Function.cantor_surjective (f := fun p : Prop => ({p} : Set Prop))
  exact?

example : False := by
  have hcard : Fintype.card (Set Prop) = 4 := by simp [Set]
  have hp : Fintype.card Prop = 2 := by native_decide
  exact?
