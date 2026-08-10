import Mathlib

def a (n : ℕ) : ℕ := 0

inductive MyType (k' : ℕ) : Type where
  | inl : (Nonempty (a (6 * (k' + 5)) ≠ 4)) → MyType k'
  | inr : (a (6 * (k' + 5)) = 4 → MyType k') → MyType k'

partial def my_dummy (k' : ℕ) (h : a (6 * (k' + 5)) = 4) : MyType k' :=
  MyType.inr (fun _ => my_dummy k' h)

instance instMyTypeNonempty (k' : ℕ) : Nonempty (MyType k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨my_dummy k' h⟩
  · exact ⟨MyType.inl ⟨h⟩⟩
