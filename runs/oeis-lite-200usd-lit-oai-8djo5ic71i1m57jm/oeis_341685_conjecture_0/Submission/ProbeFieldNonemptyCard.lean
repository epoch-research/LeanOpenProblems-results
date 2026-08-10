import FormalConjectures.Util.ProblemImports
#check Field.nonempty_iff
#check Cardinal.mk_empty
#check Cardinal.mk_punit
#check Cardinal.natCast_eq_zero

example : ¬ Nonempty (Field Empty) := by
  rw [Field.nonempty_iff]
  simp

example : ¬ Nonempty (Field PUnit) := by
  rw [Field.nonempty_iff]
  simp

example : Nonempty (Field ℕ) := by
  rw [Field.nonempty_iff]
  simp [Cardinal.infinite_iff.mp (inferInstance : Infinite ℕ)]
