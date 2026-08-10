import Mathlib

noncomputable def or_to_sum {P Q : Prop} (h : P ∨ Q) : PLift P ⊕ PLift Q := by
  by_cases hP : P
  · exact Sum.inl ⟨hP⟩
  · have hQ : Q := h.resolve_left hP
    exact Sum.inr ⟨hQ⟩
