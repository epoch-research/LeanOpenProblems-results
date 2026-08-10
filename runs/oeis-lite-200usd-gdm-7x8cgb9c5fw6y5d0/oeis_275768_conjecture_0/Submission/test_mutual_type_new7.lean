import Mathlib

open Nat

def a (n : ℕ) : ℕ := if n = 30 then 5 else 0

inductive MyType (k' : ℕ) : Type where
  | inl : (Nonempty (a (6 * (k' + 5)) ≠ 4)) → MyType k'
  | inr : (a (6 * (k' + 5)) = 4) → (MyType k' → False) → MyType k'

instance instMyTypeNonempty (k' : ℕ) : Nonempty (MyType k') := by
  rcases Classical.em (Nonempty (MyType k')) with h | h
  · exact h
  · have h_empty : MyType k' → False := fun x => h ⟨x⟩
    have h_eq : a (6 * (k' + 5)) = 4 := by
      by_contra h_ne
      exact h ⟨MyType.inl ⟨h_ne⟩⟩
    have val : MyType k' := MyType.inr h_eq h_empty
    exact ⟨val⟩
