import FormalConjectures.Util.ProblemImports

example : ¬ (Classical.choose (show ∃ z : ℤ, z = 0 from ⟨0, rfl⟩) =
             Classical.choose (show ∃ z : ℤ, z = 1 from ⟨1, rfl⟩)) := by
  norm_num

example : (show (∃ z : ℤ, z = 0) from ⟨0, rfl⟩) = (show (∃ z : ℤ, z = 0) from ⟨0, rfl⟩) := rfl

example : (∃ z : ℤ, z = 0) = (∃ z : ℤ, z = 1) := by
  apply propext
  constructor <;> intro _ <;> exact ⟨by norm_num, by norm_num⟩

-- attempt direct equality via prop equality
example : Classical.choose (show ∃ z : ℤ, z = 0 from ⟨0, rfl⟩) =
             Classical.choose (show ∃ z : ℤ, z = 1 from ⟨1, rfl⟩) := by
  let hP : (∃ z : ℤ, z = 0) = (∃ z : ℤ, z = 1) := by
    apply propext; constructor <;> intro _ <;> exact ⟨by norm_num, by norm_num⟩
  -- exact ?_
  fail_if_success cases hP
  -- can't use hP to rewrite true into false witness equality
  norm_num
