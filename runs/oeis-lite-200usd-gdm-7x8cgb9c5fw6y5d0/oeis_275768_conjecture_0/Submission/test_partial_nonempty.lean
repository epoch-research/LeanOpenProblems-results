import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ := 0

inductive MyType (k' : ℕ) : Type where
  | inl : (Nonempty (a (6 * (k' + 5)) ≠ 4)) → MyType k'
  | inr : (a (6 * (k' + 5)) = 4 → MyType k') → MyType k'

partial def get_nonempty (k' : ℕ) : Nonempty (MyType k') :=
  if h : a (6 * (k' + 5)) = 4 then
    have : Nonempty (MyType k') := get_nonempty k'
    ⟨MyType.inr (fun _ => Classical.choice this)⟩
  else
    ⟨MyType.inl ⟨h⟩⟩

instance (k' : ℕ) : Nonempty (MyType k') := get_nonempty k'
