import Mathlib
import Submission.Spec
import Submission.Proof11
import Submission.Proof7

open Nat BigOperators

lemma P_pos (n : ℕ) (hn2 : n > 2) :
  (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) > 0 := by
  apply Finset.prod_pos
  intro k hk
  rw [Finset.mem_Ico] at hk
  have h1 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk.1
  have h2 : 2 ^ 1 = 2 := rfl
  omega
