import FormalConjectures.Util.ProblemImports

/--
A270994: $a(n) = 9454129 + 11184810 \cdot n$.
-/
def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

/-- A natural number `k` is a Sierpiński number if it is odd, greater than 1,
    and for all positive natural numbers `n`, $k \cdot 2^n + 1$ is not a prime number. -/
def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)


def n_sol : ℕ := 5319426

lemma k_val : a n_sol + 4 = 59496778573193 := by
  decide

lemma k_mod_3 : (a n_sol + 4) % 3 = 2 := by decide
lemma k_mod_5 : (a n_sol + 4) % 5 = 3 := by decide
lemma k_mod_7 : (a n_sol + 4) % 7 = 3 := by decide
lemma k_mod_17 : (a n_sol + 4) % 17 = 8 := by decide
lemma k_mod_257 : (a n_sol + 4) % 257 = 249 := by decide
lemma k_mod_97 : (a n_sol + 4) % 97 = 3 := by decide
lemma k_mod_673 : (a n_sol + 4) % 673 = 8 := by decide

lemma not_prime_of_dvd {n d : ℕ} (hd : d ∣ n) (h1 : d ≠ 1) (hn : d ≠ n) : ¬ n.Prime := by
  intro hp
  have h := hp.eq_one_or_self_of_dvd d hd
  rcases h with h | h
  · exact h1 h
  · exact hn h

lemma pow_mod_eq {P o r : ℕ} (ho : 2^o % P = 1) (m : ℕ) (h_eq : m % o = r) :
  2^m % P = 2^r % P := by
  have h_div : m = o * (m / o) + r := by
    rw [← h_eq]
    exact (Nat.div_add_mod m o).symm
  rw [h_div]
  rw [pow_add, pow_mul]
  have h_pow : (2^o)^(m / o) % P = 1 % P := by
    rw [Nat.pow_mod, ho]
    simp
  rw [Nat.mul_mod, h_pow, ← Nat.mul_mod]
  simp

lemma dvd_of_pow_mod_eq {P o r k m : ℕ} (ho : 2^o % P = 1) (hk : (k * 2^r + 1) % P = 0)
  (h_eq : m % o = r) : P ∣ k * 2^m + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have h_mul : (k * 2^m + 1) % P = (k * 2^r + 1) % P := by
    rw [Nat.add_mod, Nat.mul_mod, pow_mod_eq ho m h_eq, ← Nat.mul_mod, ← Nat.add_mod]
  rw [h_mul, hk]

lemma k_pow_gt {k P : ℕ} (m : ℕ) (hk : k > P) : k * 2^m + 1 > P := by
  have h2 : 2^m ≥ 1 := Nat.one_le_pow m 2 (by decide)
  have h3 : k * 2^m ≥ k * 1 := Nat.mul_le_mul_left k h2
  rw [mul_one] at h3
  omega

lemma k_not_prime (m : ℕ) : ¬ Nat.Prime ((a n_sol + 4) * 2^m + 1) := by
  have h_or : m % 48 = 0 ∨ m % 48 = 1 ∨ m % 48 = 2 ∨ m % 48 = 3 ∨ m % 48 = 4 ∨ m % 48 = 5 ∨ m % 48 = 6 ∨ m % 48 = 7 ∨ m % 48 = 8 ∨ m % 48 = 9 ∨ m % 48 = 10 ∨ m % 48 = 11 ∨ m % 48 = 12 ∨ m % 48 = 13 ∨ m % 48 = 14 ∨ m % 48 = 15 ∨ m % 48 = 16 ∨ m % 48 = 17 ∨ m % 48 = 18 ∨ m % 48 = 19 ∨ m % 48 = 20 ∨ m % 48 = 21 ∨ m % 48 = 22 ∨ m % 48 = 23 ∨ m % 48 = 24 ∨ m % 48 = 25 ∨ m % 48 = 26 ∨ m % 48 = 27 ∨ m % 48 = 28 ∨ m % 48 = 29 ∨ m % 48 = 30 ∨ m % 48 = 31 ∨ m % 48 = 32 ∨ m % 48 = 33 ∨ m % 48 = 34 ∨ m % 48 = 35 ∨ m % 48 = 36 ∨ m % 48 = 37 ∨ m % 48 = 38 ∨ m % 48 = 39 ∨ m % 48 = 40 ∨ m % 48 = 41 ∨ m % 48 = 42 ∨ m % 48 = 43 ∨ m % 48 = 44 ∨ m % 48 = 45 ∨ m % 48 = 46 ∨ m % 48 = 47 := by omega
  rcases h_or with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · -- m % 48 = 0
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 1
    have h_eq : m % 8 = 1 := by omega
    have hd : 17 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 17 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 17 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 2
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 3
    have h_eq : m % 4 = 3 := by omega
    have hd : 5 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 5 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 5 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 4
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 5
    have h_eq : m % 48 = 5 := by omega
    have hd : 97 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 97 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 97 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 6
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 7
    have h_eq : m % 4 = 3 := by omega
    have hd : 5 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 5 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 5 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 8
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 9
    have h_eq : m % 8 = 1 := by omega
    have hd : 17 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 17 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 17 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 10
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 11
    have h_eq : m % 4 = 3 := by omega
    have hd : 5 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 5 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 5 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 12
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 13
    have h_eq : m % 16 = 13 := by omega
    have hd : 257 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 257 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 257 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 14
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 15
    have h_eq : m % 4 = 3 := by omega
    have hd : 5 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 5 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 5 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 16
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 17
    have h_eq : m % 8 = 1 := by omega
    have hd : 17 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 17 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 17 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 18
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 19
    have h_eq : m % 4 = 3 := by omega
    have hd : 5 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 5 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 5 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 20
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 21
    have h_eq : m % 48 = 21 := by omega
    have hd : 673 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 673 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 673 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 22
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 23
    have h_eq : m % 4 = 3 := by omega
    have hd : 5 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 5 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 5 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 24
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 25
    have h_eq : m % 8 = 1 := by omega
    have hd : 17 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 17 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 17 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 26
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 27
    have h_eq : m % 4 = 3 := by omega
    have hd : 5 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 5 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 5 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 28
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 29
    have h_eq : m % 16 = 13 := by omega
    have hd : 257 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 257 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 257 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 30
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 31
    have h_eq : m % 4 = 3 := by omega
    have hd : 5 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 5 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 5 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 32
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 33
    have h_eq : m % 8 = 1 := by omega
    have hd : 17 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 17 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 17 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 34
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 35
    have h_eq : m % 4 = 3 := by omega
    have hd : 5 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 5 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 5 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 36
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 37
    have h_eq : m % 3 = 1 := by omega
    have hd : 7 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 7 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 7 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 38
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 39
    have h_eq : m % 4 = 3 := by omega
    have hd : 5 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 5 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 5 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 40
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 41
    have h_eq : m % 8 = 1 := by omega
    have hd : 17 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 17 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 17 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 42
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 43
    have h_eq : m % 4 = 3 := by omega
    have hd : 5 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 5 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 5 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 44
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 45
    have h_eq : m % 16 = 13 := by omega
    have hd : 257 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 257 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 257 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 46
    have h_eq : m % 2 = 0 := by omega
    have hd : 3 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 3 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 3 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn
  · -- m % 48 = 47
    have h_eq : m % 4 = 3 := by omega
    have hd : 5 ∣ (a n_sol + 4) * 2^m + 1 := dvd_of_pow_mod_eq (by decide) (by decide) h_eq
    have hn : 5 ≠ (a n_sol + 4) * 2^m + 1 := by
      have hg := @k_pow_gt (a n_sol + 4) 5 m (by rw [k_val]; decide)
      omega
    exact not_prime_of_dvd hd (by decide) hn




lemma k_is_sierpinski : is_sierpinski_number (a n_sol + 4) := by
  unfold is_sierpinski_number
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · intro m hm
    exact k_not_prime m


theorem oeis_270994_conjecture_0.disproof :
  ¬ (∀ n : ℕ, is_sierpinski_number (a n) ∧ is_sierpinski_number (a n + 28) ∧ (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False)) := by
  intro h
  have h_sol := h n_sol
  rcases h_sol with ⟨_, _, h3⟩
  have h_lt1 : a n_sol < a n_sol + 4 := by omega
  have h_lt2 : a n_sol + 4 < a n_sol + 28 := by omega
  exact h3 (a n_sol + 4) k_is_sierpinski h_lt1 h_lt2
