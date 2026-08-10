import FormalConjectures.Util.ProblemImports

example (h0 : ∃ z : ℤ, z = 0) :
    HEq (Classical.choose h0) (Classical.choose (cast (by
      apply propext; constructor <;> intro _
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩) h0 : ∃ z : ℤ, z = 1)) := by
  refine dcongr_heq ?h (fun t₁ t₂ => congrFun rfl) ?f
  · exact cast_heq (by
      apply propext; constructor <;> intro _
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩) h0 |>.symm
  · intro heqProp heqFam
    -- goal?
    exact HEq.rfl

theorem bad_choose : (0:ℤ) = 1 := by
  let h0 : ∃ z : ℤ, z = 0 := ⟨0, rfl⟩
  have hh : HEq (Classical.choose h0) (Classical.choose (cast (by
      apply propext; constructor <;> intro _
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩) h0 : ∃ z : ℤ, z = 1)) := by
    refine dcongr_heq ?h (fun t₁ t₂ => congrFun rfl) ?f
    · exact cast_heq (by
        apply propext; constructor <;> intro _
        · exact ⟨1, rfl⟩
        · exact ⟨0, rfl⟩) h0 |>.symm
    · intro heqProp heqFam
      exact HEq.rfl
  have echoose : Classical.choose h0 = Classical.choose (cast (by
      apply propext; constructor <;> intro _
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩) h0 : ∃ z : ℤ, z = 1) := eq_of_heq hh
  have s0 : Classical.choose h0 = 0 := Classical.choose_spec h0
  have s1 : Classical.choose (cast (by
      apply propext; constructor <;> intro _
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩) h0 : ∃ z : ℤ, z = 1) = 1 := Classical.choose_spec _
  rw [s0, s1] at echoose
  exact echoose

#print axioms bad_choose
