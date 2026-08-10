import Mathlib

open Nat

def a (n : ℕ) : ℕ := if n = 30 then 5 else 0

inductive MyType (k' : ℕ) : Type where
  | inl : (Nonempty (a (6 * (k' + 5)) ≠ 4)) → MyType k'
  | inr : (a (6 * (k' + 5)) = 4 → MyType k') → MyType k'

partial def get_mytype_nonempty (k' : ℕ) : PLift (Nonempty (MyType k')) := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · have f : a (6 * (k' + 5)) = 4 → MyType k' := by
      intro _
      exact Classical.choice (get_mytype_nonempty k').down
    exact ⟨⟨MyType.inr f⟩⟩
  · exact ⟨⟨MyType.inl ⟨h⟩⟩⟩
