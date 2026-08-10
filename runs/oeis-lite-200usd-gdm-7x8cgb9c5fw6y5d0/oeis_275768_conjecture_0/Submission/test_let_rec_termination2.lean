import Mathlib

def a (n : ℕ) : ℕ := 0

inductive MyType (k' : ℕ) : Type where
  | inl : Nonempty (a (6 * (k' + 5)) ≠ 4) → MyType k'
  | inr : (PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4) → MyType k') → MyType k'

instance (k' : ℕ) : Nonempty (MyType k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · have h_term : MyType k' := by
      let rec f (x : PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4)) : MyType k' :=
        match x with
        | Sum.inl ⟨h_ne⟩ => MyType.inl h_ne
        | Sum.inr ⟨h_eq⟩ => MyType.inr f
      termination_by x => 0
      exact MyType.inr f
    exact ⟨h_term⟩
  · exact ⟨MyType.inl ⟨h⟩⟩
