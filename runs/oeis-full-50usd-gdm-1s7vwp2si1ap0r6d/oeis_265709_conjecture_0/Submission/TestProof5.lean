import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : (sigma 1) p = p + 1 := by
  rw [sigma_one_apply, hp.divisors]
  have h1 : 1 ≠ p := hp.ne_one.symm
  rw [sum_insert (by simp [h1]), sum_singleton, add_comm]

lemma p_add_one_dvd_sigma (p : ℕ) (hp : p.Prime) (k : ℕ) :
  p + 1 ∣ sigma 1 (p^(2*k + 1)) := by
  induction k with
  | zero =>
    simp
    rw [sigma_one_prime hp]
  | succ k ih =>
    -- 2 * (k + 1) + 1 = 2 * k + 3
    have h_eq : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by omega
    have h_sum : sigma 1 (p^(2*(k+1) + 1)) = sigma 1 (p^(2*k + 1)) + p^(2*k + 2) + p^(2*k + 3) := by
      rw [sigma_one_apply, Nat.divisors_prime_pow hp (2*(k+1) + 1)]
      rw [sigma_one_apply, Nat.divisors_prime_pow hp (2*k + 1)]
      rw [sum_map, sum_map]
      -- range (2*k + 3 + 1) is range (2*k + 4)
      -- range (2*k + 1 + 1) is range (2*k + 2)
      have h_range : range (2*k + 4) = range (2*k + 2) ∪ {2*k + 2, 2*k + 3} := by
        -- range and insert
        sorry
      sorry
    sorry
