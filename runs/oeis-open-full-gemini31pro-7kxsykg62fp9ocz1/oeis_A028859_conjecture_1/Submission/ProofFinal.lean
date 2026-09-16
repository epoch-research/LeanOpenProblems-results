import Submission.ProofLength
import Submission.ProofS2
import Submission.ProofNodupFinal
import Submission.ProofSurj
import Mathlib

set_option linter.unusedVariables false

theorem isValid2_iff_S (n : ℕ) (x : Fin (n + 1) → ℕ) :
  isValid2 x ↔ x ∈ { σ : Fin (n + 1) → ℕ |
      (n + 1) > 0 ∧
      (∀ i : Fin (n + 1), σ i > 0) ∧
      let max_val := Finset.sup Finset.univ σ
      (∀ k : ℕ, 1 ≤ k ∧ k ≤ max_val → ∃ i : Fin (n + 1), σ i = k) ∧
      (∀ i j : Fin (n + 1), i < j → j.val ≠ i.val + 1 → σ i ≥ σ j)
    } := by rfl

theorem set_eq_S (n : ℕ) :
  (List.toFinset (gen (n + 1))).toSet = { σ : Fin (n + 1) → ℕ |
      (n + 1) > 0 ∧
      (∀ i : Fin (n + 1), σ i > 0) ∧
      let max_val := Finset.sup Finset.univ σ
      (∀ k : ℕ, 1 ≤ k ∧ k ≤ max_val → ∃ i : Fin (n + 1), σ i = k) ∧
      (∀ i j : Fin (n + 1), i < j → j.val ≠ i.val + 1 → σ i ≥ σ j)
    } := by
  ext x
  rw [List.mem_toFinset]
  rw [←isValid2_iff_S]
  constructor
  · intro h
    exact gen_is_valid2 (n + 1) (by omega) x h
  · intro h
    exact surj_gen (n + 1) x h (by omega)

theorem conjecture_true (n : ℕ) :
  let L := n + 1
  let Sequence := Fin L → ℕ
  let S : Set Sequence :=
    { σ : Sequence |
      L > 0 ∧
      (∀ i : Fin L, σ i > 0) ∧
      let max_val := Finset.sup Finset.univ σ
      (∀ k : ℕ, 1 ≤ k ∧ k ≤ max_val → ∃ i : Fin L, σ i = k) ∧
      (∀ i j : Fin L, i < j → j.val ≠ i.val + 1 → σ i ≥ σ j)
    }
  ∃ (F : Finset Sequence), F.toSet = S ∧ F.card = a n := by
  use List.toFinset (gen (n + 1))
  constructor
  · exact set_eq_S n
  · have h_len := gen_length n
    have h_nodup := nodup_gen (n + 1)
    rw [List.toFinset_card_of_nodup h_nodup]
    exact h_len
