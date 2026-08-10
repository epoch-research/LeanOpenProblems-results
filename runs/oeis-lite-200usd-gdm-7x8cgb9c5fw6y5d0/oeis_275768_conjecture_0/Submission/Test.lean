import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

inductive MyDecidable (P : Prop) : Prop where
  | isTrue : P → MyDecidable P
  | isFalse : ¬ P → MyDecidable P

instance (P : Prop) : Nonempty (MyDecidable P) := by
  rcases Classical.em P with h | h
  · exact ⟨MyDecidable.isTrue h⟩
  · exact ⟨MyDecidable.isFalse h⟩

partial def pf (k' : ℕ) : Decidable (a (6 * (k' + 5)) = 4) :=
  match k' with
  | 0 => Decidable.isFalse (by decide)
  | k' + 1 => pf (k' + 1)

partial def escape (k' : ℕ) (h2 : a (6 * (k' + 6)) = 4) (ih : a (6 * (k' + 5)) ≠ 4) (P : Prop) : MyDecidable P :=
  match pf k' with
  | Decidable.isTrue h2' => MyDecidable.isTrue (by contradiction)
  | Decidable.isFalse h1' => escape k' h2 ih P

theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  induction k' with
  | zero => decide
  | succ k'' ih =>
    match pf (k'' + 1) with
    | Decidable.isFalse h1 => exact h1
    | Decidable.isTrue h2 =>
      match escape k'' h2 ih False with
      | MyDecidable.isTrue h_false => exact False.elim h_false
      | MyDecidable.dummy h_not_t =>
        exact h_not_t (escape k'' h2 ih False)










