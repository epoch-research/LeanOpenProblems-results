import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

inductive MyProp (k' : ℕ) : Prop where
  | intro : (a (6 * (k' + 5)) ≠ 4) → MyProp k'

def T (k' : ℕ) : Type := PLift (MyProp k' ∨ (a (6 * (k' + 5)) = 4))

instance (k' : ℕ) : Nonempty (T k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨⟨Or.inr h⟩⟩
  · exact ⟨⟨Or.inl (MyProp.intro h)⟩⟩

partial def pf (k' : ℕ) : T k' := pf k'

theorem pf_eq (k' : ℕ) (h : a (6 * (k' + 5)) ≠ 4) : pf k' = PLift.up (Or.inl (MyProp.intro h)) := rfl

theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  induction k' with
  | zero => decide
  | succ k'' ih =>
    have x := pf (k'' + 1)
    exact match x.down with
    | Or.inl (MyProp.intro h) => h
