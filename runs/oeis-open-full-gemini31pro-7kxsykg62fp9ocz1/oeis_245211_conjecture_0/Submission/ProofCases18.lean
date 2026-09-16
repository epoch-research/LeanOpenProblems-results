import Mathlib
import Submission.ProofCases16

open Nat Finset

lemma a_le_tau_mul_sigma {n : ℕ} (hn : 0 < n) :
  (∑ d ∈ n.divisors.erase n, (d : ℚ) * (Nat.divisors d).card) ≤
  n * ((Nat.divisors n).card * ∑ d ∈ n.divisors, (1 / (d : ℚ))) - n * (Nat.divisors n).card := by
  have h_F := F_le_tau_mul_sigma hn
  have h_in : n ∈ n.divisors := by rw [Nat.mem_divisors]; exact ⟨dvd_refl n, hn.ne.symm⟩
  have h_split := Finset.sum_erase_add n.divisors (fun d => (d : ℚ) * (Nat.divisors d).card) h_in
  rw [add_comm] at h_split
  rw [← h_split] at h_F
  linarith
