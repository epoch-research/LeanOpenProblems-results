import Mathlib

open Nat

def a (n : ℕ) : ℕ := if n = 30 then 5 else 0

instance (n : ℕ) : Decidable (a n = 4) := Nat.decEq (a n) 4

inductive MyType (k' : ℕ) : Type where
  | inl : (Nonempty (a (6 * (k' + 5)) ≠ 4)) → MyType k'
  | inr : (a (6 * (k' + 5)) = 4 → MyType k') → MyType k'

partial def get_mytype_nonempty (k' : ℕ) : PLift (Nonempty (MyType k')) :=
  if h : a (6 * (k' + 5)) = 4 then
    have f : a (6 * (k' + 5)) = 4 → MyType k' := by
      intro _
      exact Classical.choice (get_mytype_nonempty k').down
    ⟨⟨MyType.inr f⟩⟩
  else
    ⟨⟨MyType.inl ⟨h⟩⟩⟩
