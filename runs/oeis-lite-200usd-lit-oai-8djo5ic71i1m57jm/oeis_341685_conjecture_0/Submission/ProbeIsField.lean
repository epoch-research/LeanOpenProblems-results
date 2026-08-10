import FormalConjectures.Util.ProblemImports
#check Field.toIsField
#check IsField.of_field
#check field_iff_isField
example : False := by
  letI : Field ℤ := Classical.choice (Infinite.nonempty_field (α := ℤ))
  have hif : IsField ℤ := Field.toIsField ℤ
  exact Int.not_isField hif
