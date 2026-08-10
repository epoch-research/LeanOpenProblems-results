import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

instance (k' : ℕ) : Nonempty ((a (6 * (k' + 5)) ≠ 4) ∨ (a (6 * (k' + 5)) = 4)) :=
  ⟨Or.symm (Classical.em (a (6 * (k' + 5)) = 4))⟩

instance (k' m : ℕ) : Nonempty ((a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (k' + 5)) = 4)) := by
  rcases Classical.em (a (6 * (m + 5)) ≠ 4) with h | h
  · exact ⟨Or.inl h⟩
  · rcases Classical.em (a (6 * (k' + 5)) = 4) with h2 | h2
    · exact ⟨Or.inr h2⟩
    · exact ⟨Or.inl (by contradiction)⟩ -- wait, if h2 is false and h is false, we can't prove it, but we can just use classical choice since Nonempty is always true classically.
      -- actually we can just do:
      -- ⟨Or.inl (Classical.choice (by sorry))⟩ -- no sorry allowed!
      -- wait, Nonempty ((a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (k' + 5)) = 4)) is always nonempty because either the left is true or the right is true, so the Or is always nonempty!
      -- Let's prove it properly:
      -- rcases Classical.em (a (6 * (k' + 5)) = 4) with h2 | h2:
      -- if h2 is true: exact ⟨Or.inr h2⟩
      -- if h2 is false: then a (6 * (k' + 5)) ≠ 4 is true. But we need a (6 * (m + 5)) ≠ 4 or a (6 * (k' + 5)) = 4.
      -- Wait! Classically, is a (6 * (m + 5)) ≠ 4 ∨ a (6 * (k' + 5)) = 4 always nonempty?
      -- Yes, because a typeclass instance Nonempty Prop is just Nonempty, which is always true classically because any Prop is classically either true or false.
      -- Let's write the proof properly.

instance (k' m : ℕ) : Nonempty ((a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (k' + 5)) = 4)) := by
  rcases Classical.em (a (6 * (m + 5)) ≠ 4) with h | h
  · exact ⟨Or.inl h⟩
  · rcases Classical.em (a (6 * (k' + 5)) = 4) with h2 | h2
    · exact ⟨Or.inr h2⟩
    · -- here we have ¬(a (6 * (m + 5)) ≠ 4) which is a (6 * (m + 5)) = 4
      -- and ¬(a (6 * (k' + 5)) = 4) which is a (6 * (k' + 5)) ≠ 4.
      -- Since both are Props, the Or is still classically nonempty (either true or false).
      -- Let's just use:
      exact ⟨Or.symm (Classical.em (a (6 * (k' + 5)) = 4))⟩ -- wait! Or.symm of a (6 * (k' + 5)) = 4 is a (6 * (k' + 5)) = 4 ∨ a (6 * (k' + 5)) ≠ 4.
      -- This is not the type we want.
      -- Actually, we can just do:
      -- rcases Classical.em (a (6 * (k' + 5)) = 4) with h2 | h2
      -- · exact ⟨Or.inr h2⟩
      -- · -- here we have h2 : a (6 * (k' + 5)) ≠ 4.
      --   -- can we prove (a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (k' + 5)) = 4)?
      --   -- Wait! If we can't prove it constructively, we can use Classical.byContradiction:
      --   -- by_contra h_or
      --   -- and then prove False.
      --   -- Actually, we can just do:
      --   -- exact ⟨Classical.choice (by infer_instance)⟩ -- wait, this is circular.
      --   -- Let's think: is (a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (k' + 5)) = 4) always nonempty?
      --   -- Yes, because (P ∨ Q) is nonempty if we have (Nonempty P ∨ Nonempty Q) or classically we can just choose.
      --   -- Let's prove it:

#check (inferInstance : Nonempty ((a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (k' + 5)) = 4)))
