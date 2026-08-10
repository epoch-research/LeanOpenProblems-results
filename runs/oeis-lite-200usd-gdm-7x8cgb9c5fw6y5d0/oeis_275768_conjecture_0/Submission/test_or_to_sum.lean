import Mathlib

noncomputable def or_to_sum {P Q : Prop} (h : P ∨ Q) : PLift P ⊕ PLift Q := by
  rcases Classical.em P with hP | hP
  · exact Sum.inl ⟨hP⟩
  · rcases h with hP_inst | hQ_inst
    · exact False.elim (hP hP_inst)
    · exact Sum.inr ⟨hQ_inst⟩
