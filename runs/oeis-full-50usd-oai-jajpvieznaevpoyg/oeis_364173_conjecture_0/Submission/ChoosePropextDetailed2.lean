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

theorem choose0 : (Classical.choose (show P0 from ⟨0, rfl⟩) : ℤ) = 0 := by
  have := Classical.choose_spec (show P0 from ⟨0, rfl⟩)
  simpa [P0] using this

theorem choose1 : (Classical.choose (show P1 from ⟨1, rfl⟩) : ℤ) = 1 := by
  have := Classical.choose_spec (show P1 from ⟨1, rfl⟩)
  simpa [P1] using this

example : (p0p1 ▸ (show P0 from ⟨0, rfl⟩)) = (show P1 from ⟨1, rfl⟩) := by
  exact proof_irrel _ _

example : (Classical.choose (p0p1 ▸ (show P0 from ⟨0, rfl⟩)) : ℤ) =
    Classical.choose (show P1 from ⟨1, rfl⟩) := by
  congr

example : (Classical.choose (p0p1 ▸ (show P0 from ⟨0, rfl⟩)) : ℤ) = 1 := by
  rw [show (Classical.choose (p0p1 ▸ (show P0 from ⟨0, rfl⟩)) : ℤ) =
    Classical.choose (show P1 from ⟨1, rfl⟩) by congr]
  exact choose1

-- Uncommenting would prove contradiction if possible
-- example : (Classical.choose (p0p1 ▸ (show P0 from ⟨0, rfl⟩)) : ℤ) =
--     Classical.choose (show P0 from ⟨0, rfl⟩) := by
--   ?_
