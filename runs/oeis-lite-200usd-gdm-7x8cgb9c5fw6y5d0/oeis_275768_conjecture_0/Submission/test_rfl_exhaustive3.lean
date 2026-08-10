import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

instance (k' : ℕ) : Nonempty ((a (6 * (k' + 5)) ≠ 4) ∨ (a (6 * (k' + 5)) = 4)) :=
  ⟨Or.symm (Classical.em (a (6 * (k' + 5)) = 4))⟩

instance (k' m : ℕ) : Nonempty ((a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (m + 5)) = 4 ∧ (a (6 * (k' + 5)) = 4 ∨ (a (6 * (k' + 5)) ≠ 4 ∧ (a (6 * (m + 5)) = 4 → a (6 * (k' + 5)) = 4 ∨ (a (6 * (m + 5)) = 4 ∧ a (6 * (k' + 5)) ≠ 4)))))) := by
  rcases Classical.em (a (6 * (m + 5)) ≠ 4) with h | h
  · exact ⟨Or.inl h⟩
  · have h_eq : a (6 * (m + 5)) = 4 := by
      by_contra h_contra
      exact h h_contra
    rcases Classical.em (a (6 * (k' + 5)) = 4) with h2 | h2
    · exact ⟨Or.inr ⟨h_eq, Or.inl h2⟩⟩
    · have h_imp : a (6 * (m + 5)) = 4 → a (6 * (k' + 5)) = 4 ∨ (a (6 * (m + 5)) = 4 ∧ a (6 * (k' + 5)) ≠ 4) := by
        intro hm
        exact Or.inr ⟨hm, h2⟩
      exact ⟨Or.inr ⟨h_eq, Or.inr ⟨h2, h_imp⟩⟩⟩

mutual
  partial def pf (k' : ℕ) : (a (6 * (k' + 5)) ≠ 4) ∨ (a (6 * (k' + 5)) = 4) :=
    match k' with
    | 0 => Or.inl (by decide)
    | k' + 1 =>
      match pf k' with
      | Or.inl h1 => pf (k' + 1)
      | Or.inr h2 =>
        match h_rec k' k' h2 with
        | Or.inl h_rec_1 => False.elim (h_rec_1 h2)
        | Or.inr h_rec_2 => pf (k' + 1)

  partial def h_rec (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) :
      (a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (m + 5)) = 4 ∧ (a (6 * (k' + 5)) = 4 ∨ (a (6 * (k' + 5)) ≠ 4 ∧ (a (6 * (m + 5)) = 4 → a (6 * (k' + 5)) = 4 ∨ (a (6 * (m + 5)) = 4 ∧ a (6 * (k' + 5)) ≠ 4))))) :=
    match m with
    | 0 => by
      have h_dec : a 30 = 5 := by decide
      rw [h_dec] at hm4
      contradiction
    | m' + 1 => by
      match pf m' with
      | Or.inl h1' => exact h_rec k' (m' + 1) hm4
      | Or.inr h2' =>
        match h_rec k' m' h2' with
        | Or.inl h_res_1 => exact False.elim (h_res_1 h2')
        | Or.inr h_res_2 =>
          rcases h_res_2.right with h_eq | h_and
          · exact Or.inr ⟨hm4, Or.inl h_eq⟩
          · match h_and.right h2' with
            | Or.inl h_eq => exact False.elim (h_and.left h_eq)
            | Or.inr h_and2 =>
              exact Or.inr ⟨hm4, Or.inr ⟨h_and2.right, fun hm6 => Or.inr ⟨hm6, h_and2.right⟩⟩⟩
end

theorem pf_eq (k' : ℕ) (h : a (6 * (k' + 5)) ≠ 4) : pf k' = Or.inl h := rfl

theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  induction k' with
  | zero => decide
  | succ k'' ih =>
    have h_pf : pf (k'' + 1) = pf (k'' + 1) := rfl
    -- Let's generalize pf (k'' + 1) and match on it with the equality proof h_pf
    match h_val : pf (k'' + 1) with
    | Or.inl h => exact h
    | Or.inr h2 =>
      -- we have h_val : pf (k'' + 1) = Or.inr h2
      -- and we have pf_eq (k'' + 1) (main_case (k'' + 1)) : pf (k'' + 1) = Or.inl (main_case (k'' + 1))
      -- So Or.inl (main_case (k'' + 1)) = Or.inr h2 !
      have h_eq_inl : pf (k'' + 1) = Or.inl (main_case (k'' + 1)) := rfl
      rw [h_eq_inl] at h_val
      contradiction
