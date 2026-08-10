import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

def HRecType (fuel : ℕ) (k' : ℕ) (m : ℕ) : Prop :=
  match fuel with
  | 0 => True
  | fuel' + 1 => (a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (m + 5)) = 4 ∧ (a (6 * (k' + 5)) = 4 ∨ (a (6 * (k' + 5)) ≠ 4 ∧ (a (6 * (m + 5)) = 4 → a (6 * (k' + 5)) = 4))))

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
            match h_rec (fuel'' + 1) k'' k'' h2 with
            | Or.inl h_rec_1 => False.elim (h_rec_1 h2)
            | Or.inr h_rec_2 => pf (fuel'' + 1) (k'' + 1)

  def h_rec (fuel : ℕ) (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) : HRecType fuel k' m :=
    match fuel with
    | 0 => True.intro
    | fuel' + 1 =>
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
            -- fuel' = 0, so we can prove HRecType (0 + 1) k' m by using Classical.em
            match Classical.em (a (6 * (k' + 5)) = 4) with
            | Or.inl h => exact Or.inr ⟨hm4, Or.inl h⟩
            | Or.inr h => exact Or.inr ⟨hm4, Or.inr ⟨h, fun _ => h2'⟩⟩
          | fuel'' + 1 =>
            -- fuel' = fuel'' + 1 > 0, so we can recurse on h_rec!
            match h_rec (fuel'' + 1) k' m' h2' with
            | Or.inl h_res_1 => exact Or.inl (by contradiction)
            | Or.inr h_res_2 =>
              rcases h_res_2.right with h_eq | h_ne_and
              · exact Or.inr ⟨hm4, Or.inl h_eq⟩
              · have h_imp := h_ne_and.right
                have h_eq : a (6 * (k' + 5)) = 4 := h_imp h2'
                exact Or.inr ⟨hm4, Or.inl h_eq⟩
        | Or.inl h1' =>
          -- if pf fuel' m' is Or.inl h1', we can just recurse on h_rec!
          -- Wait!
          -- h_rec (fuel' + 1) k' (m' + 1) hm4 has return type HRecType (fuel' + 1) k' (m' + 1).
          -- But the recursive call h_rec fuel' k' (m' + 1) hm4 has return type HRecType fuel' k' (m' + 1).
          -- Can we convert HRecType fuel' k' (m' + 1) to HRecType (fuel' + 1) k' (m' + 1)?
          -- If we match on fuel' first!
          match fuel' with
          | 0 =>
            -- fuel' = 0, so HRecType (0 + 1) k' (m' + 1) is the real type.
            -- can we prove it?
            -- yes, because h1' has type a (6 * (m' + 5)) ≠ 4, which is the left side of Or!
            exact Or.inl h1'
          | fuel'' + 1 =>
            -- fuel' = fuel'' + 1, so the return type of the recursive call is HRecType (fuel'' + 1) k' (m' + 1),
            -- which is exactly HRecType (fuel' + 1) k' (m' + 1) ?
            -- No, fuel' + 1 is fuel'' + 2, so the recursive call has fuel'' + 1, but we need fuel'' + 2!
            -- So they are still different!
            sorry
end
