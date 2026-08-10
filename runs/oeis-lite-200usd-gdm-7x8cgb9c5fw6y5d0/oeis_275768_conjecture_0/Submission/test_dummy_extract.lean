import Mathlib

def a (n : ℕ) : ℕ := 0

inductive MyType (k' : ℕ) : Type where
  | inl : (Nonempty (a (6 * (k' + 5)) ≠ 4)) → MyType k'
  | inr : (a (6 * (k' + 5)) = 4 → MyType k') → MyType k'
  | dummy : MyType k'

instance (k' : ℕ) : Nonempty (MyType k') := ⟨MyType.dummy⟩

partial def extract_false (k' : ℕ) (h_eq : a (6 * (k' + 5)) = 4) (m : MyType k') : PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) :=
  match m with
  | MyType.inl h_ne => ⟨h_ne⟩
  | MyType.inr f => extract_false k' h_eq (f h_eq)
  | MyType.dummy => extract_false k' h_eq m
