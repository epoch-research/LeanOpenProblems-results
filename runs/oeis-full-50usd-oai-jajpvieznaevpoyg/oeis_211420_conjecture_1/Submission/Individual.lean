import Submission.Work

open Nat

-- Sketch target for a future reduced proof: each single linear factor has bounded denominator.
def Csingle (k : ℕ) : ℕ := (3 * (2*k+1)).factorial

lemma dTerm_dvd_a_mul_Csingle (n k : ℕ) : dTerm n k ∣ a n * Csingle k := by
  rw [← Nat.factorization_le_iff_dvd (dTerm_ne_zero n k) (mul_ne_zero (a_ne_zero n) (by unfold Csingle; exact (Nat.factorial_pos _).ne'))]
  rw [Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul (a_ne_zero n) (by unfold Csingle; exact (Nat.factorial_pos _).ne')]
    -- This should follow by splitting exponents `i ≤ (dTerm n k).factorization p`:
    -- small powers `p^i ≤ 3(2k+1)` are paid by `Csingle`, large powers by `a` via `good_floor`.
    sorry
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
