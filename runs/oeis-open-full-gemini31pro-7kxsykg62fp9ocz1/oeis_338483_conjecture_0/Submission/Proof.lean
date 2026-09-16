import Submission.Spec
import Mathlib

open Nat Finset Set

lemma a_le_of_mem (n : ℕ) (m : ℕ) (hm : A047983_count m = n) : a n ≤ m := by
  dsimp [a]
  have h_mem : m ∈ {m | A047983_count m = n} := hm
  exact csInf_le (OrderBot.bddBelow _) h_mem

theorem disproof_thm : ¬ ∃ n : ℕ, n > 0 ∧ Nat.Prime (a n) ∧ a n > 31 := by
  sorry
