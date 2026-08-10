import Mathlib

def a (n : ℕ) : ℕ := 0

inductive MyType (k' : ℕ) : Type where
  | inl : (Nonempty (a (6 * (k' + 5)) ≠ 4)) → MyType k'
  | inr : (a (6 * (k' + 5)) = 4 → MyType k') → MyType k'

instance instMyTypeNonempty (k' : ℕ) : Nonempty (MyType k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · let rec f (h2 : a (6 * (k' + 5)) = 4) : MyType k' :=
      MyType.inr (fun _ => f h2)
    exact ⟨f h⟩
  · exact ⟨MyType.inl ⟨h⟩⟩
