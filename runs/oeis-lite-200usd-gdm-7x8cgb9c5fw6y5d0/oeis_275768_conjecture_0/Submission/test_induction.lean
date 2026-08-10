import Mathlib

def a (n : ℕ) : ℕ := 0

inductive MyType (k' : ℕ) : Type where
  | inl : (Nonempty (a (6 * (k' + 5)) ≠ 4)) → MyType k'
  | inr : (a (6 * (k' + 5)) = 4 → MyType k') → MyType k'

instance instNonemptyExtract (k' : ℕ) : Nonempty (a (6 * (k' + 5)) = 4 → MyType k' ⊕ PLift (a (6 * (k' + 5)) = 4) → PLift (Nonempty (a (6 * (k' + 5)) ≠ 4))) := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · have h_empty : MyType k' → False := by
      intro x
      induction x with
      | inl h_ne => exact (Classical.choice h_ne) h
      | inr f ih => exact ih h
    have h_empty_sum : MyType k' ⊕ PLift (a (6 * (k' + 5)) = 4) → False := by
      intro x
      rcases x with x | ⟨h_eq⟩
      · exact h_empty x
      · exact h.elim (fun h_ne => h_ne h_eq)
    exact ⟨fun _ x => False.elim (h_empty_sum x)⟩
  · exact ⟨fun _ _ => ⟨⟨h⟩⟩⟩
