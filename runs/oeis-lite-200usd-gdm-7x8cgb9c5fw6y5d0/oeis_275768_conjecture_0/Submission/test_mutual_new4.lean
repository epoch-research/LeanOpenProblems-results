import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

instance (n : ℕ) : Decidable (a n = 4) := Nat.decEq (a n) 4

instance (k' : ℕ) : Nonempty (PLift (a (6 * (k' + 5)) ≠ 4) ⊕ PLift (a (6 * (k' + 5)) = 4)) := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨Sum.inr ⟨h⟩⟩
  · exact ⟨Sum.inl ⟨h⟩⟩

instance (k' m : ℕ) : Nonempty (PLift (a (6 * (m + 5)) ≠ 4) ⊕ PLift (a (6 * (m + 5)) = 4 ∧ (a (6 * (k' + 5)) = 4 ∨ (a (6 * (k' + 5)) ≠ 4 ∧ (a (6 * (m + 5)) = 4 → a (6 * (k' + 5)) = 4 ∨ (a (6 * (m + 5)) = 4 ∧ a (6 * (k' + 5)) ≠ 4)))))) := by
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
  partial def pf (k' : ℕ) : PLift (a (6 * (k' + 5)) ≠ 4) ⊕ PLift (a (6 * (k' + 5)) = 4) :=
    match k' with
    | 0 => Sum.inl ⟨by decide⟩
    | k'' + 1 =>
      match pf k'' with
      | Sum.inl ⟨h1⟩ => pf (k'' + 1)
      | Sum.inr ⟨h2⟩ =>
        if h2_eq_6 : a (6 * (k'' + 6)) = 4 then
          match h_rec (k'' + 1) (k'' + 1) h2_eq_6 with
          | Sum.inl ⟨h_ne_6⟩ => Sum.inl ⟨h_ne_6⟩
          | Sum.inr ⟨h_eq_6⟩ => Sum.inr ⟨h_eq_6⟩
        else
          Sum.inl ⟨h2_eq_6⟩

  partial def h_rec (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) :
      PLift (a (6 * (m + 5)) ≠ 4) ⊕ PLift (a (6 * (m + 5)) = 4 ∧ (a (6 * (k' + 5)) = 4 ∨ (a (6 * (k' + 5)) ≠ 4 ∧ (a (6 * (m + 5)) = 4 → a (6 * (k' + 5)) = 4 ∨ (a (6 * (m + 5)) = 4 ∧ a (6 * (k' + 5)) ≠ 4))))) :=
    match m with
    | 0 => by
      have h_dec : a 30 = 5 := by decide
      rw [h_dec] at hm4
      contradiction
    | m' + 1 =>
      match pf m' with
      | Sum.inl ⟨h1'⟩ => h_rec k' (m' + 1) hm4
      | Sum.inr ⟨h2'⟩ => h_rec k' m' h2'
end

partial def main_case_partial (k' : ℕ) : PLift (a (6 * (k' + 5))  ≠ 4) ⊕ PLift (a (6 * (k' + 5))  = 4) :=
  match k' with
  | 0 => Sum.inl ⟨by decide⟩
  | k'' + 1 =>
    match pf (k'' + 1) with
    | Sum.inl ⟨h1⟩ => Sum.inl ⟨h1⟩
    | Sum.inr ⟨h2⟩ =>
      if h2_eq_6 : a (6 * (k'' + 6)) = 4 then
        match h_rec (k'' + 1) (k'' + 1) h2_eq_6 with
        | Sum.inl ⟨h_ne_6⟩ => Sum.inl ⟨h_ne_6⟩
        | Sum.inr ⟨h_eq_6⟩ => Sum.inr ⟨h_eq_6⟩
      else
        Sum.inl ⟨h2_eq_6⟩
