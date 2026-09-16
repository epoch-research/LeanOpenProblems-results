import Mathlib
import Submission.ProofCases22
import Submission.ProofCases5
import Submission.ProofBound
import Submission.ProofFinal

open Nat Finset

lemma a_bound_pk3 {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
  a (p ^ k) < p ^ k := by
  have hd : a (p ^ k) = ∑ j ∈ range k, (j + 1) * p ^ j := a_pk p k hp
  rw [hd]
  have h_bound : ∑ j ∈ range k, (j + 1) * p ^ j < p ^ k := by
    induction' k, hk using Nat.le_induction with k hk ih
    · have : ∑ j ∈ range 2, (j + 1) * p ^ j = 1 + 2 * p := by
        rw [sum_range_succ, sum_range_one]
        ring
      rw [this]
      have hp2 : 2 ≤ p := hp.two_le
      have hp_sq : p * p = p ^ 2 := by ring
      have hp3 : 3 ≤ p := by
        by_cases h_eq2 : p = 2
        · exfalso
          have h_eq3 : p ^ 2 = 4 := by rw [h_eq2]; rfl
          rw [h_eq3] at hd
          rw [this] at hd
          have h_val : a 4 = 5 := by rfl
          rw [h_val] at hd
          have h_sum2 : ∑ j ∈ range 2, (j + 1) * 2 ^ j = 5 := by rfl
          have h_false : 5 = 5 := rfl
          revert h_false; decide
        · have := hp.two_le; omega
      have h_lt : 1 + 2 * p < p * p := by
        calc 1 + 2 * p < p + 2 * p := by omega
          _ = 3 * p := by ring
          _ ≤ p * p := Nat.mul_le_mul_right p hp3
      omega
    · sorry
  exact h_bound
