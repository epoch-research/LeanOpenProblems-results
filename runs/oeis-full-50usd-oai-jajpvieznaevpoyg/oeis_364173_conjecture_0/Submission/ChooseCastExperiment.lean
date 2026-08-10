import FormalConjectures.Util.ProblemImports

example : (∃ z : ℤ, z = 0) = (∃ z : ℤ, z = 1) := by
  apply propext
  constructor <;> intro _
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

example (h0 : ∃ z : ℤ, z = 0) (h1 : ∃ z : ℤ, z = 1) :
    Classical.choose (cast (by
      apply propext; constructor <;> intro _
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩) h0) = Classical.choose h1 := by
  -- same existential proposition (after cast) so proof irrelevance should give proof equality
  have hp : cast (by
      apply propext; constructor <;> intro _
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩) h0 = h1 := proof_irrel _ _
  rw [hp]

-- Can we connect choose of cast proof to original choose? This should fail.
example (h0 : ∃ z : ℤ, z = 0) (h1 : ∃ z : ℤ, z = 1) :
    Classical.choose h0 = Classical.choose h1 := by
  have hp : (∃ z : ℤ, z = 0) = (∃ z : ℤ, z = 1) := by
    apply propext; constructor <;> intro _
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  have hc : Classical.choose (cast hp h0) = Classical.choose h1 := by
    have : cast hp h0 = h1 := proof_irrel _ _
    rw [this]
  -- no relation between choose h0 and choose (cast hp h0)
  fail_if_success exact hc
  sorry
