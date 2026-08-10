import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 2000000
set_option maxRecDepth 2000000

theorem not_prime_of_dvd (N p : ℕ) (h_div : p ∣ N) (h1 : 1 < p) (h2 : p < N) : ¬ Nat.Prime N := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd p h_div with hp1 | hp2
  · rw [hp1] at h1
    exact Nat.lt_irrefl 1 h1
  · rw [hp2] at h2
    exact Nat.lt_irrefl N h2

lemma bound_helper (p n : ℕ) (hp : p < 10 ^ 9) (hn : 9 ≤ 2 ^ n) : p < 10 ^ (2 ^ n) + 1 := by
  have h_le : 10 ^ 9 ≤ 10 ^ (2 ^ n) + 1 := by
    have h_le_pow : 10 ^ 9 ≤ 10 ^ (2 ^ n) := Nat.pow_le_pow_right (by decide) hn
    exact Nat.le_add_right_of_le h_le_pow
  exact Nat.lt_of_lt_of_le hp h_le

theorem not_prime_10_2_17 : ¬ Nat.Prime (10 ^ (2 ^ 17) + 1) := by
  have h_div : 175636481 ∣ 10 ^ (2 ^ 17) + 1 := Nat.dvd_of_mod_eq_zero (by decide)
  exact not_prime_of_dvd _ 175636481 h_div (by decide) (bound_helper _ 17 (by decide) (by decide))

