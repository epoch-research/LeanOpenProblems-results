import Mathlib

open List

lemma adjacent_of_no_between {L : List ℕ} (hS : L.Pairwise (· < ·))
    {a b : ℕ} (ha : a ∈ L) (hb : b ∈ L) (hab : a < b) 
    (h_no : ∀ x ∈ L, ¬ (a < x ∧ x < b)) : (a, b) ∈ L.zip L.tail := by
  induction L with
  | nil => contradiction
  | cons y ys ih =>
    cases ha with
    | head _ =>
      cases hb with
      | head _ =>
        exfalso
        exact lt_irrefl _ hab
      | tail _ hbt =>
        cases ys with
        | nil => contradiction
        | cons z zs =>
          cases hbt with
          | head _ =>
            exact Mem.head _
          | tail _ hbtt =>
            exfalso
            have haz : a < z := rel_of_pairwise_cons hS (Mem.head _)
            have hS_tail : Pairwise (· < ·) (z :: zs) := Pairwise.of_cons hS
            have hzb : z < b := rel_of_pairwise_cons hS_tail hbtt
            have hz_in : z ∈ a :: z :: zs := Mem.tail _ (Mem.head _)
            exact h_no z hz_in ⟨haz, hzb⟩
    | tail _ hat =>
      cases hb with
      | head _ =>
        exfalso
        have hba : b < a := rel_of_pairwise_cons hS hat
        omega
      | tail _ hbt =>
        have h_zip_tail : (y :: ys).zip (y :: ys).tail = (y, ys.headI) :: (ys.zip ys.tail) := by
          cases ys with
          | nil => contradiction
          | cons z zs => rfl
        rw [h_zip_tail]
        apply Mem.tail
        apply ih (Pairwise.of_cons hS) hat hbt
        intro x hx
        exact h_no x (Mem.tail _ hx)

