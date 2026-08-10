import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

mutual
  def pf (fuel : ℕ) (k' : ℕ) : (a (6 * (k' + 5)) ≠ 4) ∨ (a (6 * (k' + 5)) = 4) :=
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
      (a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (m + 5)) = 4 ∧ (a (6 * (k' + 5)) = 4 ∨ (a (6 * (k' + 5)) ≠ 4 ∧ (a (6 * (m + 5)) = 4 → (fuel = 0 → False) → a (6 * (k' + 5)) = 4)))) :=
    match fuel with
    | 0 =>
      match Classical.em (a (6 * (k' + 5)) = 4) with
      | Or.inl h => Or.inr ⟨hm4, Or.inl h⟩
      | Or.inr h => Or.inr ⟨hm4, Or.inr ⟨h, fun _ h_fuel => False.elim (h_fuel rfl)⟩⟩
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
                -- wait, we have h_imp : a (6 * (m' + 5)) = 4 → (fuel' = 0 → False) → a (6 * (k' + 5)) = 4.
                -- and we have h2' : a (6 * (m' + 5)) = 4.
                -- we need to prove fuel' = 0 → False.
                -- but we don't know if fuel' = 0!
                -- wait, why do we need (fuel' = 0 → False)?
                sorry
              exact Or.inr ⟨hm4, Or.inl h_eq⟩
        | Or.inl h1' => exact h_rec fuel' k' (m' + 1) hm4
end
