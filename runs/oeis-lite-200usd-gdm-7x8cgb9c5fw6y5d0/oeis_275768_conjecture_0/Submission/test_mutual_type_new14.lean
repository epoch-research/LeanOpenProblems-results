import Mathlib

open Nat

def a (n : ℕ) : ℕ := if n = 30 then 5 else 0

inductive MainTypeTwo (k'' : ℕ) : Type where
  | inl : PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4)) → MainTypeTwo k''
  | inr : PLift (a (6 * (k'' + 5)) = 4) → MainTypeTwo k''
  | dummy : (Nonempty (MainTypeTwo k'') → False) → MainTypeTwo k''

instance inst_MainTypeTwo (k'' : ℕ) : Nonempty (MainTypeTwo k'') := by
  rcases Classical.em (Nonempty (MainTypeTwo k'')) with h | h
  · exact h
  · exact ⟨MainTypeTwo.dummy h⟩
