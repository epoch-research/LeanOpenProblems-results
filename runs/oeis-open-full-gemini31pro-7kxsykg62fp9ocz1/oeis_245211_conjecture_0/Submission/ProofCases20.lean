import Mathlib
import Submission.ProofCases19
import Submission.ProofCases9
import Submission.ProofBound
import Submission.ProofFinal

open Nat Finset

lemma bound_sigma_div_n_k_primes {p k : ℕ} (hp : p.Prime) :
  ∑ d ∈ (p ^ k).divisors, (1 / (d : ℚ)) = (1 - (1 / (p : ℚ)) ^ (k + 1)) / (1 - 1 / (p : ℚ)) := by
  have hd : (p ^ k).divisors = (range (k + 1)).map ⟨fun x => p ^ x, fun x y h => (Nat.pow_right_injective hp.two_le h)⟩ := by
    exact Nat.divisors_prime_pow hp k
  rw [hd, sum_map]
  have h_eq : (fun x => 1 / ((p ^ x : ℕ) : ℚ)) = (fun x => 1 / (p : ℚ) ^ x) := by
    ext x
    rw [Nat.cast_pow]
  have h_eq2 : (∑ x ∈ range (k + 1), 1 / ((Function.Embedding.mk (fun x => p ^ x) (Nat.pow_right_injective hp.two_le) x : ℕ) : ℚ)) = ∑ x ∈ range (k + 1), 1 / ((p ^ x : ℕ) : ℚ) := rfl
  rw [h_eq2, sum_congr rfl (fun x _ => congr_fun h_eq x)]
  have h_geom := my_geom_sum_eq (k := k) hp.two_le
  exact h_geom
