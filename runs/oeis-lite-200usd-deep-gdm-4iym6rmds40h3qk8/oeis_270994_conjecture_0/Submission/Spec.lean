import FormalConjectures.Util.ProblemImports

open Nat

/--
A270994: $a(n) = 9454129 + 11184810 \cdot n$.
-/
def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

lemma a_odd (n : ℕ) : (a n) % 2 = 1 := by
  dsimp [a]
  omega

lemma a_gt_1 (n : ℕ) : (a n) > 1 := by
  dsimp [a]
  omega

/-- A natural number `k` is a Sierpiński number if it is odd, greater than 1,
    and for all positive natural numbers `n`, $k \cdot 2^n + 1$ is not a prime number. -/
def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)

theorem two_pow_modEq_general (p g m r : ℕ) (hp : (2^g) % p = 1) (hm : m % g = r) (hp2 : p > 1) :
  (2^m) % p = (2^r) % p := by
  have h : m = g * (m / g) + r := by
    rw [← hm]
    exact (Nat.div_add_mod m g).symm
  rw [h]
  rw [pow_add, pow_mul]
  rw [Nat.mul_mod]
  rw [Nat.pow_mod]
  rw [hp]
  rw [one_pow]
  rw [Nat.mod_eq_of_lt hp2]
  rw [one_mul]
  rw [Nat.mod_mod]

def K : ℕ := 5292270077783

lemma K_sierpinski : is_sierpinski_number K := by
  refine ⟨by decide, by decide, ?_⟩
  intro m hm pm
  have h_mod : m % 48 < 48 := Nat.mod_lt _ (by decide)
  interval_cases h_cases : m % 48
  · -- case r = 0
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 1
    have h_pow : (2^m) % 7 = (2^1) % 7 := by
      have h_m_g : m % 3 = 1 := by omega
      have h_div : (2^3) % 7 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 7 3 m 1 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 7 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 7 < K * 2^m + 1 := by
      have h_k_lt : 7 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 2
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 3
    have h_pow : (2^m) % 5 = (2^3) % 5 := by
      have h_m_g : m % 4 = 3 := by omega
      have h_div : (2^4) % 5 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 5 4 m 3 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 5 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 5 < K * 2^m + 1 := by
      have h_k_lt : 5 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 4
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 5
    have h_pow : (2^m) % 257 = (2^5) % 257 := by
      have h_m_g : m % 16 = 5 := by omega
      have h_div : (2^16) % 257 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 257 16 m 5 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 257 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 257 < K * 2^m + 1 := by
      have h_k_lt : 257 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 6
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 7
    have h_pow : (2^m) % 5 = (2^3) % 5 := by
      have h_m_g : m % 4 = 3 := by omega
      have h_div : (2^4) % 5 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 5 4 m 3 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 5 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 5 < K * 2^m + 1 := by
      have h_k_lt : 5 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 8
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 9
    have h_pow : (2^m) % 17 = (2^1) % 17 := by
      have h_m_g : m % 8 = 1 := by omega
      have h_div : (2^8) % 17 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 17 8 m 1 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 17 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 17 < K * 2^m + 1 := by
      have h_k_lt : 17 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 10
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 11
    have h_pow : (2^m) % 5 = (2^3) % 5 := by
      have h_m_g : m % 4 = 3 := by omega
      have h_div : (2^4) % 5 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 5 4 m 3 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 5 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 5 < K * 2^m + 1 := by
      have h_k_lt : 5 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 12
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 13
    have h_pow : (2^m) % 7 = (2^1) % 7 := by
      have h_m_g : m % 3 = 1 := by omega
      have h_div : (2^3) % 7 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 7 3 m 1 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 7 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 7 < K * 2^m + 1 := by
      have h_k_lt : 7 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 14
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 15
    have h_pow : (2^m) % 5 = (2^3) % 5 := by
      have h_m_g : m % 4 = 3 := by omega
      have h_div : (2^4) % 5 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 5 4 m 3 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 5 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 5 < K * 2^m + 1 := by
      have h_k_lt : 5 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 16
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 17
    have h_pow : (2^m) % 17 = (2^1) % 17 := by
      have h_m_g : m % 8 = 1 := by omega
      have h_div : (2^8) % 17 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 17 8 m 1 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 17 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 17 < K * 2^m + 1 := by
      have h_k_lt : 17 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 18
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 19
    have h_pow : (2^m) % 5 = (2^3) % 5 := by
      have h_m_g : m % 4 = 3 := by omega
      have h_div : (2^4) % 5 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 5 4 m 3 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 5 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 5 < K * 2^m + 1 := by
      have h_k_lt : 5 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 20
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 21
    have h_pow : (2^m) % 257 = (2^5) % 257 := by
      have h_m_g : m % 16 = 5 := by omega
      have h_div : (2^16) % 257 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 257 16 m 5 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 257 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 257 < K * 2^m + 1 := by
      have h_k_lt : 257 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 22
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 23
    have h_pow : (2^m) % 5 = (2^3) % 5 := by
      have h_m_g : m % 4 = 3 := by omega
      have h_div : (2^4) % 5 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 5 4 m 3 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 5 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 5 < K * 2^m + 1 := by
      have h_k_lt : 5 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 24
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 25
    have h_pow : (2^m) % 7 = (2^1) % 7 := by
      have h_m_g : m % 3 = 1 := by omega
      have h_div : (2^3) % 7 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 7 3 m 1 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 7 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 7 < K * 2^m + 1 := by
      have h_k_lt : 7 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 26
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 27
    have h_pow : (2^m) % 5 = (2^3) % 5 := by
      have h_m_g : m % 4 = 3 := by omega
      have h_div : (2^4) % 5 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 5 4 m 3 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 5 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 5 < K * 2^m + 1 := by
      have h_k_lt : 5 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 28
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 29
    have h_pow : (2^m) % 97 = (2^29) % 97 := by
      have h_m_g : m % 48 = 29 := by omega
      have h_div : (2^48) % 97 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 97 48 m 29 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 97 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 97 < K * 2^m + 1 := by
      have h_k_lt : 97 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 30
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 31
    have h_pow : (2^m) % 5 = (2^3) % 5 := by
      have h_m_g : m % 4 = 3 := by omega
      have h_div : (2^4) % 5 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 5 4 m 3 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 5 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 5 < K * 2^m + 1 := by
      have h_k_lt : 5 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 32
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 33
    have h_pow : (2^m) % 17 = (2^1) % 17 := by
      have h_m_g : m % 8 = 1 := by omega
      have h_div : (2^8) % 17 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 17 8 m 1 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 17 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 17 < K * 2^m + 1 := by
      have h_k_lt : 17 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 34
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 35
    have h_pow : (2^m) % 5 = (2^3) % 5 := by
      have h_m_g : m % 4 = 3 := by omega
      have h_div : (2^4) % 5 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 5 4 m 3 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 5 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 5 < K * 2^m + 1 := by
      have h_k_lt : 5 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 36
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 37
    have h_pow : (2^m) % 7 = (2^1) % 7 := by
      have h_m_g : m % 3 = 1 := by omega
      have h_div : (2^3) % 7 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 7 3 m 1 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 7 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 7 < K * 2^m + 1 := by
      have h_k_lt : 7 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 38
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 39
    have h_pow : (2^m) % 5 = (2^3) % 5 := by
      have h_m_g : m % 4 = 3 := by omega
      have h_div : (2^4) % 5 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 5 4 m 3 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 5 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 5 < K * 2^m + 1 := by
      have h_k_lt : 5 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 40
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 41
    have h_pow : (2^m) % 17 = (2^1) % 17 := by
      have h_m_g : m % 8 = 1 := by omega
      have h_div : (2^8) % 17 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 17 8 m 1 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 17 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 17 < K * 2^m + 1 := by
      have h_k_lt : 17 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 42
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 43
    have h_pow : (2^m) % 5 = (2^3) % 5 := by
      have h_m_g : m % 4 = 3 := by omega
      have h_div : (2^4) % 5 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 5 4 m 3 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 5 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 5 < K * 2^m + 1 := by
      have h_k_lt : 5 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 44
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 45
    have h_pow : (2^m) % 673 = (2^45) % 673 := by
      have h_m_g : m % 48 = 45 := by omega
      have h_div : (2^48) % 673 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 673 48 m 45 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 673 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 673 < K * 2^m + 1 := by
      have h_k_lt : 673 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 46
    have h_pow : (2^m) % 3 = (2^0) % 3 := by
      have h_m_g : m % 2 = 0 := by omega
      have h_div : (2^2) % 3 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 3 2 m 0 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 3 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 3 < K * 2^m + 1 := by
      have h_k_lt : 3 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm
  · -- case r = 47
    have h_pow : (2^m) % 5 = (2^3) % 5 := by
      have h_m_g : m % 4 = 3 := by omega
      have h_div : (2^4) % 5 = 1 := by decide
      have h_pow_mod := two_pow_modEq_general 5 4 m 3 h_div h_m_g (by decide)
      exact h_pow_mod
    have h_dvd : 5 ∣ K * 2^m + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mul_mod, h_pow]
      decide
    have h_lt : 5 < K * 2^m + 1 := by
      have h_k_lt : 5 < K * 2^m + 1 := by dsimp [K]; omega
      exact h_k_lt
    exact Nat.not_prime_of_dvd_of_lt h_dvd (by decide) h_lt pm

theorem oeis_270994_conjecture_0.disproof : ¬ (∀ n : ℕ,
  is_sierpinski_number (a n) ∧
  is_sierpinski_number (a n + 28) ∧
  (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False)) := by
  intro h
  have h_n := h 473165
  have h_between := h_n.2.2
  have h_k := K_sierpinski
  have h_gt : a 473165 < K := by
    dsimp [a, K]
    decide
  have h_lt : K < a 473165 + 28 := by
    dsimp [a, K]
    decide
  exact h_between K h_k h_gt h_lt
