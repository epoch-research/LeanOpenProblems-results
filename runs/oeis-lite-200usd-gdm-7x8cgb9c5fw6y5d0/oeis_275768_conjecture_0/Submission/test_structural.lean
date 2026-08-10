import Mathlib

def a (n : ℕ) : ℕ := 0

inductive MyType (k' : ℕ) : Type where
  | inl : (Nonempty (a (6 * (k' + 5)) ≠ 4)) → MyType k'
  | inr : (a (6 * (k' + 5)) = 4 → MyType k') → MyType k'

def extract_ne (k' : ℕ) (x : MyType k') : Nonempty (a (6 * (k' + 5)) ≠ 4) :=
  match x with
  | MyType.inl h_ne => h_ne
  | MyType.inr f =>
    rcases Classical.em (a (6 * (k' + 5)) = 4) with h_eq | h_ne
    · exact extract_ne k' (f h_eq)
    · exact ⟨h_ne⟩
