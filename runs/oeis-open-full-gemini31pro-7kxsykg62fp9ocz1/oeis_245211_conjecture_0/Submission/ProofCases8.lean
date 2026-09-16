import Submission.Spec
import Mathlib
import Submission.ProofCases7

open Nat Finset

lemma sum_inv_subset {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hdvd : m ∣ n) :
  ∑ d ∈ m.divisors, 1 / (d : ℚ) ≤ ∑ d ∈ n.divisors, 1 / (d : ℚ) := by
  have h_sub : m.divisors ⊆ n.divisors := by
    intro d hd
    rw [mem_divisors] at hd ⊢
    exact ⟨dvd_trans hd.1 hdvd, hn.ne.symm⟩
  apply sum_le_sum_of_subset_of_nonneg h_sub
  intro i _ _
  positivity
