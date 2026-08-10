import Mathlib

def a (n : ℕ) : ℕ := 0

inductive MainTypeTwo (k'' : ℕ) : Type where
  | inl : PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4)) → MainTypeTwo k''
  | inr : PLift (a (6 * (k'' + 5)) = 4) → MainTypeTwo k''
  | dummy : (MainTypeTwo k'' → False) → MainTypeTwo k''

instance inst_MainTypeTwo (k'' : ℕ) : Nonempty (MainTypeTwo k'') := by
  rcases Classical.em (Nonempty (MainTypeTwo k'')) with h | h
  · exact h
  · have h_empty : MainTypeTwo k'' → False := by
      intro x
      exact h ⟨x⟩
    exact ⟨MainTypeTwo.dummy h_empty⟩
