import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

inductive MyType : ℕ → Type where
  | inl : (k' : ℕ) → (Nonempty (a (6 * (k' + 5))  ≠ 4)) → MyType k'
  | inr : (k' : ℕ) → (a (6 * (k' + 4)) = 4 → MyType k') → MyType k'

instance instNonemptyMyType (k' : ℕ) [ih : Nonempty (a (6 * (k' + 5)) ≠ 4)] : Nonempty (MyType (k' + 1)) :=
  ⟨MyType.inr (k' + 1) (fun h => False.elim ((Classical.choice ih) h))⟩

instance (k'' : ℕ) : Nonempty (MyType (k'' + 1) ⊕ PLift (a (6 * (k'' + 5)) = 4)) := by
  rcases Classical.em (a (6 * (k'' + 5)) = 4) with h | h
  · exact ⟨Sum.inr ⟨h⟩⟩
  · have h_ne : Nonempty (a (6 * (k'' + 5)) ≠ 4) := ⟨h⟩
    have inst := @inferInstance (Nonempty (MyType (k'' + 1))) (instNonemptyMyType k'' (ih := h_ne))
    rcases inst with ⟨m⟩
    exact ⟨Sum.inl m⟩
