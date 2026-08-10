import FormalConjectures.Util.ProblemImports

example (P Q : ℤ → Prop) (he : (∃ x, P x) = (∃ x, Q x)) (hP : ∃ x, P x) :
    HEq (Classical.choose hP) (Classical.choose (cast he hP)) := by
  have hh : HEq hP (cast he hP) := cast_heq he hP |>.symm
  -- Try hcongr for @Classical.choose? Need functions HEq
  -- @Classical.choose Int P hP and @Classical.choose Int Q (cast he hP)
  change HEq (@Classical.choose ℤ P hP) (@Classical.choose ℤ Q (cast he hP))
  -- function f = @Classical.choose ℤ P, g = @Classical.choose ℤ Q
  have hf : HEq (@Classical.choose ℤ P) (@Classical.choose ℤ Q) := ?_
  exact congr_heq hf hh

example (h0 : ∃ z : ℤ, z = 0) :
    Classical.choose h0 = Classical.choose (cast (by
      apply propext; constructor <;> intro _
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩) h0 : ∃ z : ℤ, z = 1) := by
  have hh : HEq (Classical.choose h0) (Classical.choose (cast (by
      apply propext; constructor <;> intro _
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩) h0 : ∃ z : ℤ, z = 1)) := by
    apply?
  exact eq_of_heq hh
