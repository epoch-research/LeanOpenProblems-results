import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

mutual
  def pf (k' : ℕ) : (a (6 * (k' + 5)) ≠ 4) ∨ (a (6 * (k' + 5)) = 4) :=
    match k' with
    | 0 => Or.inl (by decide)
    | k'' + 1 =>
      match pf k'' with
      | Or.inl h1 => Or.inl (by sorry) -- wait, we still can't prove this without math
      | Or.inr h2 =>
        match h_rec k'' k'' h2 with
        | Or.inl h_rec_1 => False.elim (h_rec_1 h2)
        | Or.inr h_rec_2 => Or.inl (by sorry)
  termination_by k'

  def h_rec (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) :
      (a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (m + 5)) = 4 ∧ (a (6 * (k' + 5)) = 4 ∨ (a (6 * (k' + 5)) ≠ 4 ∧ (a (6 * (m + 5)) = 4 → a (6 * (k' + 5)) = 4)))) :=
    match m with
    | 0 => by
      have h_dec : a 30 = 5 := by decide
      rw [h_dec] at hm4
      contradiction
    | m' + 1 => by
      match pf m' with
      | Or.inr h2' =>
        match h_rec k' m' h2' with
        | Or.inl h_res_1 => exact Or.inl (by contradiction)
        | Or.inr h_res_2 =>
          rcases h_res_2.right with h_eq | h_ne_and
          · exact Or.inr ⟨hm4, Or.inl h_eq⟩
          · have h_imp := h_ne_and.right
            have h_eq : a (6 * (k' + 5)) = 4 := h_imp h2'
            exact Or.inr ⟨hm4, Or.inl h_eq⟩
      | Or.inl h1' => exact h_rec k' (m' + 1) hm4
  termination_by m
end
