import Submission.Spec
import Submission.Spec
import Mathlib

open Nat Finset


lemma a_eq_sum_proper {n : ℕ} (hn : 0 < n) :
  a n = ∑ d ∈ n.divisors.erase n, d * (Nat.divisors d).card := by
  unfold a
  have h_in : n ∈ n.divisors := by rw [Nat.mem_divisors]; exact ⟨dvd_refl n, Nat.ne_of_gt hn⟩
  have h_split := Finset.sum_erase_add n.divisors (fun d => d * (Nat.divisors d).card) h_in
  rw [add_comm] at h_split
  rw [← h_split]
  exact Nat.add_sub_cancel_left _ _

lemma a_ge_subset {n : ℕ} (hn : 0 < n) (D : Finset ℕ) (hD : D ⊆ n.divisors.erase n) :
  ∑ d ∈ D, d * (Nat.divisors d).card ≤ a n := by
  rw [a_eq_sum_proper hn]
  exact sum_le_sum_of_subset_of_nonneg hD (fun _ _ _ => Nat.zero_le _)

