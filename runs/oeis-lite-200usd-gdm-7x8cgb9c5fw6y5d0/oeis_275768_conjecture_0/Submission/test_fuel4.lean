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
      (a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (m + 5)) = 4 ∧ (a (6 * (k' + 5)) = 4 ∨ (a (6 * (k' + 5)) ≠ 4 ∧ (a (6 * (m + 5)) = 4 → a (6 * (k' + 5)) = 4)))) :=
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
        | Or.inr h => Or.inr ⟨hm4, Or.inr ⟨h, fun h_false => by
            have h_dec : a 30 = 5 := by decide -- wait, m' + 1 is not 0, so we can't use a 30 here.
            -- But wait, if fuel = 0, we can just prove the implication using Classical.em!
            -- Since the implication is: a (6 * (m + 5)) = 4 → a (6 * (k' + 5)) = 4.
            -- And we have h : a (6 * (k' + 5)) ≠ 4.
            -- Wait! If h : a (6 * (k' + 5)) ≠ 4, and we want to prove a (6 * (m + 5)) = 4 → a (6 * (k' + 5)) = 4.
            -- Since we don't have a contradiction, how can we prove it?
            -- Actually, if we just use Classical.em on the implication itself!
            sorry
        ⟩⟩
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
              have h_eq : a (6 * (k' + 5)) = 4 := h_imp h2'
              exact Or.inr ⟨hm4, Or.inl h_eq⟩
        | Or.inl h1' => exact h_rec fuel' k' (m' + 1) hm4
end
