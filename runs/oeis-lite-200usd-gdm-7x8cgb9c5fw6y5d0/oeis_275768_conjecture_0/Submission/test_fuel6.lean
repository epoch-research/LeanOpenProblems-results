import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

def HType (fuel : ℕ) (k' : ℕ) (m : ℕ) : Prop :=
  fuel > 0 → ((a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (m + 5)) = 4 ∧ (a (6 * (k' + 5)) = 4 ∨ (a (6 * (k' + 5)) ≠ 4 ∧ (a (6 * (m + 5)) = 4 → a (6 * (k' + 5)) = 4)))))

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
          match fuel' with
          | 0 =>
            match Classical.em (a (6 * (k'' + 6)) = 4) with
            | Or.inl h => Or.inr h
            | Or.inr h => Or.inl h
          | fuel'' + 1 =>
            have h_pos : fuel'' + 1 > 0 := Nat.zero_lt_succ fuel''
            match (h_rec (fuel'' + 1) k'' k'' h2) h_pos with
            | Or.inl h_rec_1 => False.elim (h_rec_1 h2)
            | Or.inr h_rec_2 => pf (fuel'' + 1) (k'' + 1)

  def h_rec (fuel : ℕ) (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) : HType fuel k' m :=
    match fuel with
    | 0 => fun h_pos => False.elim (by contradiction)
    | fuel' + 1 => fun _ =>
      match m with
      | 0 => by
        have h_dec : a 30 = 5 := by decide
        rw [h_dec] at hm4
        contradiction
      | m' + 1 => by
        match pf fuel' m' with
        | Or.inr h2' =>
          match fuel' with
          | 0 =>
            -- if fuel' = 0, we can get a contradiction since hm4 : a (6 * (m' + 1 + 5)) = 4
            -- wait, if fuel' = 0, h2' has type a (6 * (m' + 5)) = 4.
            -- but m' is not 0, so h2' is not a 30 = 4.
            -- wait! if fuel' = 0, can we get a contradiction?
            -- Actually, if fuel' = 0, we can just use Classical.em!
            match Classical.em (a (6 * (k' + 5)) = 4) with
            | Or.inl h => exact Or.inr ⟨hm4, Or.inl h⟩
            | Or.inr h =>
              -- we can prove the implication because fuel' = 0, but wait, h_rec's return type has fuel' + 1 > 0.
              -- actually, if fuel' = 0, we can just prove the implication using Classical.em!
              -- wait, if fuel' = 0, can we prove a (6 * (m' + 5)) = 4 → a (6 * (k' + 5)) = 4?
              -- No, we still can't because hm4 is true and h is false.
              sorry
          | fuel'' + 1 =>
            have h_pos' : fuel'' + 1 > 0 := Nat.zero_lt_succ fuel''
            match (h_rec (fuel'' + 1) k' m' h2') h_pos' with
            | Or.inl h_res_1 => exact Or.inl (by contradiction)
            | Or.inr h_res_2 =>
              rcases h_res_2.right with h_eq | h_ne_and
              · exact Or.inr ⟨hm4, Or.inl h_eq⟩
              · have h_imp := h_ne_and.right
                have h_eq : a (6 * (k' + 5)) = 4 := h_imp h2'
                exact Or.inr ⟨hm4, Or.inl h_eq⟩
        | Or.inl h1' =>
          have h_pos_fuel' : fuel' > 0 := by
            -- wait!
            -- If pf fuel' m' is Or.inl h1', we call h_rec fuel' k' (m' + 1) hm4.
            -- But we need to return HType (fuel' + 1) k' (m' + 1) which is (fuel' + 1) > 0 → ...
            -- And we call h_rec fuel', which returns HType fuel' k' (m' + 1).
            -- If we can prove fuel' > 0, we can apply it.
            -- But is fuel' > 0?
            -- What if fuel' = 0?
            sorry
end
