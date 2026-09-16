import Mathlib
import Submission.ProofCases20
import Submission.ProofBound
import Submission.ProofFinal

open Nat Finset

lemma a_bound_pk {p k : ℕ} (hp : p.Prime) :
  (p ^ k).divisors.sum (fun d => (d : ℚ) * (Nat.divisors d).card) =
  (p ^ k : ℚ) * ∑ j ∈ range (k + 1), ((j + 1 : ℕ) : ℚ) / (p ^ (k - j) : ℚ) := by
  have hd : (p ^ k).divisors = (range (k + 1)).map ⟨fun x => p ^ x, fun x y h => (Nat.pow_right_injective hp.two_le h)⟩ := by
    exact Nat.divisors_prime_pow hp k
  rw [hd, sum_map]
  have h_eq : (fun (x : ℕ) => ((p ^ x : ℕ) : ℚ) * ((Nat.divisors (p ^ x)).card : ℚ)) = (fun (x : ℕ) => ((p : ℚ) ^ x) * (x + 1 : ℚ)) := by
    ext x
    have h_tau : (Nat.divisors (p ^ x)).card = x + 1 := by
      rw [Nat.divisors_prime_pow hp x, card_map, card_range]
    rw [h_tau, Nat.cast_pow]
    push_cast
    rfl
  have h_eq2 : (∑ x ∈ range (k + 1), (((Function.Embedding.mk (fun x => p ^ x) (Nat.pow_right_injective hp.two_le) x : ℕ) : ℚ) * ((Nat.divisors (Function.Embedding.mk (fun x => p ^ x) (Nat.pow_right_injective hp.two_le) x)).card : ℚ))) = ∑ x ∈ range (k + 1), ((p ^ x : ℕ) : ℚ) * ((Nat.divisors (p ^ x)).card : ℚ) := rfl
  rw [h_eq2, sum_congr rfl (fun x _ => congr_fun h_eq x)]
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  have h_le : j ≤ k := by omega
  have h_pow_div : (p ^ k : ℚ) / (p ^ (k - j) : ℚ) = (p ^ j : ℚ) := by
    have hp_pos : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have h_sub : k - (k - j) = j := by omega
    have := pow_sub₀ (p : ℚ) hp_pos (by omega : k - j ≤ k)
    exact this.symm.trans (by rw [h_sub])
  have h_j1 : ((j + 1 : ℕ) : ℚ) = (j + 1 : ℚ) := by push_cast; rfl
  rw [h_j1]
  rw [← h_pow_div]
  ring
