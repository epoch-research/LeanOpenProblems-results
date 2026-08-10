import FormalConjectures.Util.ProblemImports
#check Fintype.nonempty_field_iff
#check Field.nonempty_iff
#check IsPrimePow
#synth Fact (IsPrimePow 1)
example : IsPrimePow 1 := by native_decide
example : False := by
  have hne : Nonempty (Field (Fin 1)) := (Fintype.nonempty_field_iff (α := Fin 1)).mpr (by native_decide)
  letI : Field (Fin 1) := Classical.choice hne
  exact zero_ne_one (Subsingleton.elim (0 : Fin 1) (1 : Fin 1))
