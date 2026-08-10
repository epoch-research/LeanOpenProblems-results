import FormalConjectures.Util.ProblemImports

noncomputable section

def P0 : Prop := ∃ z : ℤ, z = 0
def P1 : Prop := ∃ z : ℤ, z = 1

theorem p0p1 : P0 = P1 := by
  apply propext
  unfold P0 P1
  constructor
  · intro _; exact ⟨1, rfl⟩
  · intro _; exact ⟨0, rfl⟩

example : (Classical.choose (show P0 from ⟨0, rfl⟩) : ℤ) = 0 := by rfl
example : (Classical.choose (show P1 from ⟨1, rfl⟩) : ℤ) = 1 := by rfl

example : (Classical.choose (p0p1 ▸ (show P0 from ⟨0, rfl⟩)) : ℤ) = 1 := by rfl

#check congrArg Classical.choose

example : (p0p1 ▸ (show P0 from ⟨0, rfl⟩)) = (show P1 from ⟨1, rfl⟩) := by
  apply proof_irrel_heq -- maybe no

example : (Classical.choose (p0p1 ▸ (show P0 from ⟨0, rfl⟩)) : ℤ) =
    Classical.choose (show P1 from ⟨1, rfl⟩) := by
  congr

-- can we relate choose after cast to original?
example : (Classical.choose (p0p1 ▸ (show P0 from ⟨0, rfl⟩)) : ℤ) =
    Classical.choose (show P0 from ⟨0, rfl⟩) := by
  -- should fail
  cases p0p1
  rfl
