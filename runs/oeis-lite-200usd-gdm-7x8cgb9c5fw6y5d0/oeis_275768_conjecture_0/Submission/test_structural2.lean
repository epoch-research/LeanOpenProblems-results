import Mathlib

def a (n : ℕ) : ℕ := 0

inductive MyType (k' : ℕ) : Type where
  | inl : (Nonempty (a (6 * (k' + 5)) ≠ 4)) → MyType k'
  | inr : (a (6 * (k' + 5)) = 4 → MyType k') → MyType k'

def extract_ne (k' : ℕ) (x : MyType k') : Nonempty (a (6 * (k' + 5)) ≠ 4) := by
  induction x with
  | inl h_ne => exact h_ne
  | inr f ih =>
    by_cases h_eq : a (6 * (k' + 5)) = 4
    · exact ih h_eq
    · exact ⟨h_eq⟩
