import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

mutual
  def pf (fuel : ℕ) (k' : ℕ) : (a (6 * (k' + 5))  ≠ 4) ∨ (a (6 * (k' + 5))  = 4) :=
    match fuel with
    | 0 =>
      match Classical.em (a (6 * (k' + 5)) = 4) with
      | Or.inl h => Or.inr h
      | Or.inr h => Or.inl h
    | fuel' + 1 =>
      match k' with
      | 0 => Or.inl (by decide)
      | k'' + 1 =>
        match pf fuel' k'' with
        | Or.inl h1 => pf fuel' (k'' + 1)
        | Or.inr h2 =>
          match h_rec fuel' k'' k'' h2 with
          | Or.inl h_rec_1 => False.elim (h_rec_1 h2)
          | Or.inr h_rec_2 => pf fuel' (k'' + 1)

  def h_rec (fuel : ℕ) (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) :
      (a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (m + 5)) = 4 ∧ (a (6 * (k' + 5)) = 4 ∨ (a (6 * (k' + 5)) ≠ 4 ∧ (a (6 * (m + 5)) = 4 → (m = 0 → False) → a (6 * (k' + 5)) = 4)))) :=
    match fuel with
    | 0 =>
      match m with
      | 0 => by
        have h_dec : a 30 = 5 := by decide
        rw [h_dec] at hm4
        contradiction
      | m' + 1 =>
        match Classical.em (a (6 * (k' + 5)) = 4) with
        | Or.inl h => Or.inr ⟨hm4, Or.inl h⟩
        | Or.inr h => Or.inr ⟨hm4, Or.inr ⟨h, fun _ h_m => False.elim (h_m (by contradiction))⟩⟩
    | fuel' + 1 =>
      match m with
      | 0 => by
        have h_dec : a 30 = 5 := by decide
        rw [h_dec] at hm4
        contradiction
      | m' + 1 => by
        match pf fuel' m' with
        | Or.inr h2' =>
          match h_rec fuel' k' m' h2' with
          | Or.inl h_res_1 => exact Or.inl (by contradiction)
          | Or.inr h_res_2 =>
            rcases h_res_2.right with h_eq | h_ne_and
            · exact Or.inr ⟨hm4, Or.inl h_eq⟩
            · have h_imp := h_ne_and.right
              have h_eq : a (6 * (k' + 5)) = 4 := by
                have hm'_not_zero : m' = 0 → False := by
                  intro hm'_zero
                  subst hm'_zero
                  have h_dec : a 30 = 5 := by decide
                  rw [h_dec] at h2'
                  contradiction
                exact h_imp h2' hm'_not_zero
              exact Or.inr ⟨hm4, Or.inl h_eq⟩
        | Or.inl h1' => exact h_rec fuel' k' (m' + 1) hm4
end
