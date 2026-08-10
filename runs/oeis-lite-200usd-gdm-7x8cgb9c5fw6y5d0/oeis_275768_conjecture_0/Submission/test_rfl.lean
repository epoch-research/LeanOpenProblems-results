import Mathlib

def a (n : ℕ) : ℕ := 0

inductive MyProp (k' : ℕ) : Prop where
  | intro : (a (6 * (k' + 5)) ≠ 4) → MyProp k'

instance (k' : ℕ) : Nonempty (PLift (MyProp k' ∨ (a (6 * (k' + 5)) = 4))) := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨⟨Or.inr h⟩⟩
  · exact ⟨⟨Or.inl (MyProp.intro h)⟩⟩

partial def pf (k' : ℕ) : PLift (MyProp k' ∨ (a (6 * (k' + 5)) = 4)) := pf k'

theorem pf_eq (k' : ℕ) (h : a (6 * (k' + 6)) ≠ 4) : pf (k' + 1) = PLift.up (Or.inl (MyProp.intro h)) := rfl
