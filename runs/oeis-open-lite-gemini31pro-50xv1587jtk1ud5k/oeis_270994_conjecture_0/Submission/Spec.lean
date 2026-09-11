import FormalConjectures.Util.ProblemImports

/--
A270994: $a(n) = 9454129 + 11184810 \cdot n$.
-/
def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

/-- A natural number `k` is a Sierpiński number if it is odd, greater than 1,
    and for all positive natural numbers `n`, $k \cdot 2^n + 1$ is not a prime number. -/
def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)

/--
oeis_270994_conjecture_0: Are a(n) and a(n) + 28 always consecutive Sierpiński numbers?

This conjecture asserts that for all $n$, $a(n)$ and $a(n)+28$ are Sierpiński numbers,
and there are no Sierpiński numbers strictly between them.
-/
theorem oeis_270994_conjecture_0 : ∀ n : ℕ,
  is_sierpinski_number (a n) ∧
  is_sierpinski_number (a n + 28) ∧
  (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False) := by
  sorry


set_option maxRecDepth 2000000
set_option maxHeartbeats 0

lemma pow_mod_period (p period n q r : ℕ) (h : n = period * q + r) (h_period : 2 ^ period ≡ 1 [MOD p]) :
    2 ^ n ≡ 2 ^ r [MOD p] := by
  subst h
  have h1 : 2 ^ (period * q + r) = (2 ^ period) ^ q * 2 ^ r := by
    rw [pow_add, pow_mul]
  rw [h1]
  have h2 : (2 ^ period) ^ q ≡ 1 ^ q [MOD p] := Nat.ModEq.pow q h_period
  rw [one_pow] at h2
  have h3 : (2 ^ period) ^ q * 2 ^ r ≡ 1 * 2 ^ r [MOD p] := Nat.ModEq.mul h2 (Nat.ModEq.refl _)
  rw [one_mul] at h3
  exact h3

lemma k_pow_mod (k p period n q r : ℕ) (h : n = period * q + r) (h_period : 2 ^ period ≡ 1 [MOD p])
    (h_rem : (k * 2 ^ r + 1) % p = 0) :
    (k * 2 ^ n + 1) % p = 0 := by
  have h1 : 2 ^ n ≡ 2 ^ r [MOD p] := pow_mod_period p period n q r h h_period
  have h2 : k * 2 ^ n + 1 ≡ k * 2 ^ r + 1 [MOD p] := by
    apply Nat.ModEq.add_right
    apply Nat.ModEq.mul_left
    exact h1
  have h3 : k * 2 ^ r + 1 ≡ 0 [MOD p] := by
    exact h_rem
  exact h2.trans h3

lemma not_prime_of_dvd_of_lt (p x : ℕ) (h1 : p ∣ x) (h2 : p < x) (h3 : 1 < p) : ¬ Nat.Prime x := by
  intro hp
  have h_dvd := Nat.Prime.dvd_iff_eq hp h3.ne'
  rw [h_dvd] at h1
  omega

def k_val : ℕ := 5292270077783

lemma k_not_prime (n : ℕ) (_hn : n > 0) : ¬ Nat.Prime (k_val * 2 ^ n + 1) := by
  have h_cases : n % 48 = 0 ∨ n % 48 = 1 ∨ n % 48 = 2 ∨ n % 48 = 3 ∨ n % 48 = 4 ∨ n % 48 = 5 ∨ n % 48 = 6 ∨ n % 48 = 7 ∨ n % 48 = 8 ∨ n % 48 = 9 ∨ n % 48 = 10 ∨ n % 48 = 11 ∨ n % 48 = 12 ∨ n % 48 = 13 ∨ n % 48 = 14 ∨ n % 48 = 15 ∨ n % 48 = 16 ∨ n % 48 = 17 ∨ n % 48 = 18 ∨ n % 48 = 19 ∨ n % 48 = 20 ∨ n % 48 = 21 ∨ n % 48 = 22 ∨ n % 48 = 23 ∨ n % 48 = 24 ∨ n % 48 = 25 ∨ n % 48 = 26 ∨ n % 48 = 27 ∨ n % 48 = 28 ∨ n % 48 = 29 ∨ n % 48 = 30 ∨ n % 48 = 31 ∨ n % 48 = 32 ∨ n % 48 = 33 ∨ n % 48 = 34 ∨ n % 48 = 35 ∨ n % 48 = 36 ∨ n % 48 = 37 ∨ n % 48 = 38 ∨ n % 48 = 39 ∨ n % 48 = 40 ∨ n % 48 = 41 ∨ n % 48 = 42 ∨ n % 48 = 43 ∨ n % 48 = 44 ∨ n % 48 = 45 ∨ n % 48 = 46 ∨ n % 48 = 47 := by omega
  rcases h_cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47
  · -- case 0
    have h_rem : (k_val * 2 ^ 0 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 0 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 0 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 1
    have h_rem : (k_val * 2 ^ 1 + 1) % 7 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 7] := by rfl
    have h_div : 7 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 1 := by omega
      exact k_pow_mod k_val 7 48 n (n / 48) 1 hn_eq h_period h_rem
    have h_lt : 7 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 7 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 7 := by decide
    exact not_prime_of_dvd_of_lt 7 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 2
    have h_rem : (k_val * 2 ^ 2 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 2 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 2 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 3
    have h_rem : (k_val * 2 ^ 3 + 1) % 5 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 5] := by rfl
    have h_div : 5 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 3 := by omega
      exact k_pow_mod k_val 5 48 n (n / 48) 3 hn_eq h_period h_rem
    have h_lt : 5 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 5 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 5 := by decide
    exact not_prime_of_dvd_of_lt 5 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 4
    have h_rem : (k_val * 2 ^ 4 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 4 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 4 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 5
    have h_rem : (k_val * 2 ^ 5 + 1) % 257 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 257] := by rfl
    have h_div : 257 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 5 := by omega
      exact k_pow_mod k_val 257 48 n (n / 48) 5 hn_eq h_period h_rem
    have h_lt : 257 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 257 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 257 := by decide
    exact not_prime_of_dvd_of_lt 257 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 6
    have h_rem : (k_val * 2 ^ 6 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 6 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 6 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 7
    have h_rem : (k_val * 2 ^ 7 + 1) % 5 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 5] := by rfl
    have h_div : 5 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 7 := by omega
      exact k_pow_mod k_val 5 48 n (n / 48) 7 hn_eq h_period h_rem
    have h_lt : 5 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 5 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 5 := by decide
    exact not_prime_of_dvd_of_lt 5 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 8
    have h_rem : (k_val * 2 ^ 8 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 8 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 8 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 9
    have h_rem : (k_val * 2 ^ 9 + 1) % 17 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 17] := by rfl
    have h_div : 17 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 9 := by omega
      exact k_pow_mod k_val 17 48 n (n / 48) 9 hn_eq h_period h_rem
    have h_lt : 17 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 17 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 17 := by decide
    exact not_prime_of_dvd_of_lt 17 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 10
    have h_rem : (k_val * 2 ^ 10 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 10 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 10 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 11
    have h_rem : (k_val * 2 ^ 11 + 1) % 5 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 5] := by rfl
    have h_div : 5 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 11 := by omega
      exact k_pow_mod k_val 5 48 n (n / 48) 11 hn_eq h_period h_rem
    have h_lt : 5 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 5 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 5 := by decide
    exact not_prime_of_dvd_of_lt 5 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 12
    have h_rem : (k_val * 2 ^ 12 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 12 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 12 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 13
    have h_rem : (k_val * 2 ^ 13 + 1) % 7 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 7] := by rfl
    have h_div : 7 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 13 := by omega
      exact k_pow_mod k_val 7 48 n (n / 48) 13 hn_eq h_period h_rem
    have h_lt : 7 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 7 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 7 := by decide
    exact not_prime_of_dvd_of_lt 7 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 14
    have h_rem : (k_val * 2 ^ 14 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 14 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 14 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 15
    have h_rem : (k_val * 2 ^ 15 + 1) % 5 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 5] := by rfl
    have h_div : 5 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 15 := by omega
      exact k_pow_mod k_val 5 48 n (n / 48) 15 hn_eq h_period h_rem
    have h_lt : 5 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 5 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 5 := by decide
    exact not_prime_of_dvd_of_lt 5 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 16
    have h_rem : (k_val * 2 ^ 16 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 16 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 16 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 17
    have h_rem : (k_val * 2 ^ 17 + 1) % 17 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 17] := by rfl
    have h_div : 17 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 17 := by omega
      exact k_pow_mod k_val 17 48 n (n / 48) 17 hn_eq h_period h_rem
    have h_lt : 17 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 17 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 17 := by decide
    exact not_prime_of_dvd_of_lt 17 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 18
    have h_rem : (k_val * 2 ^ 18 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 18 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 18 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 19
    have h_rem : (k_val * 2 ^ 19 + 1) % 5 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 5] := by rfl
    have h_div : 5 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 19 := by omega
      exact k_pow_mod k_val 5 48 n (n / 48) 19 hn_eq h_period h_rem
    have h_lt : 5 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 5 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 5 := by decide
    exact not_prime_of_dvd_of_lt 5 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 20
    have h_rem : (k_val * 2 ^ 20 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 20 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 20 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 21
    have h_rem : (k_val * 2 ^ 21 + 1) % 257 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 257] := by rfl
    have h_div : 257 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 21 := by omega
      exact k_pow_mod k_val 257 48 n (n / 48) 21 hn_eq h_period h_rem
    have h_lt : 257 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 257 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 257 := by decide
    exact not_prime_of_dvd_of_lt 257 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 22
    have h_rem : (k_val * 2 ^ 22 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 22 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 22 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 23
    have h_rem : (k_val * 2 ^ 23 + 1) % 5 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 5] := by rfl
    have h_div : 5 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 23 := by omega
      exact k_pow_mod k_val 5 48 n (n / 48) 23 hn_eq h_period h_rem
    have h_lt : 5 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 5 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 5 := by decide
    exact not_prime_of_dvd_of_lt 5 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 24
    have h_rem : (k_val * 2 ^ 24 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 24 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 24 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 25
    have h_rem : (k_val * 2 ^ 25 + 1) % 7 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 7] := by rfl
    have h_div : 7 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 25 := by omega
      exact k_pow_mod k_val 7 48 n (n / 48) 25 hn_eq h_period h_rem
    have h_lt : 7 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 7 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 7 := by decide
    exact not_prime_of_dvd_of_lt 7 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 26
    have h_rem : (k_val * 2 ^ 26 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 26 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 26 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 27
    have h_rem : (k_val * 2 ^ 27 + 1) % 5 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 5] := by rfl
    have h_div : 5 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 27 := by omega
      exact k_pow_mod k_val 5 48 n (n / 48) 27 hn_eq h_period h_rem
    have h_lt : 5 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 5 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 5 := by decide
    exact not_prime_of_dvd_of_lt 5 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 28
    have h_rem : (k_val * 2 ^ 28 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 28 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 28 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 29
    have h_rem : (k_val * 2 ^ 29 + 1) % 97 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 97] := by rfl
    have h_div : 97 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 29 := by omega
      exact k_pow_mod k_val 97 48 n (n / 48) 29 hn_eq h_period h_rem
    have h_lt : 97 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 97 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 97 := by decide
    exact not_prime_of_dvd_of_lt 97 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 30
    have h_rem : (k_val * 2 ^ 30 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 30 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 30 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 31
    have h_rem : (k_val * 2 ^ 31 + 1) % 5 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 5] := by rfl
    have h_div : 5 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 31 := by omega
      exact k_pow_mod k_val 5 48 n (n / 48) 31 hn_eq h_period h_rem
    have h_lt : 5 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 5 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 5 := by decide
    exact not_prime_of_dvd_of_lt 5 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 32
    have h_rem : (k_val * 2 ^ 32 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 32 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 32 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 33
    have h_rem : (k_val * 2 ^ 33 + 1) % 17 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 17] := by rfl
    have h_div : 17 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 33 := by omega
      exact k_pow_mod k_val 17 48 n (n / 48) 33 hn_eq h_period h_rem
    have h_lt : 17 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 17 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 17 := by decide
    exact not_prime_of_dvd_of_lt 17 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 34
    have h_rem : (k_val * 2 ^ 34 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 34 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 34 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 35
    have h_rem : (k_val * 2 ^ 35 + 1) % 5 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 5] := by rfl
    have h_div : 5 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 35 := by omega
      exact k_pow_mod k_val 5 48 n (n / 48) 35 hn_eq h_period h_rem
    have h_lt : 5 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 5 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 5 := by decide
    exact not_prime_of_dvd_of_lt 5 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 36
    have h_rem : (k_val * 2 ^ 36 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 36 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 36 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 37
    have h_rem : (k_val * 2 ^ 37 + 1) % 7 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 7] := by rfl
    have h_div : 7 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 37 := by omega
      exact k_pow_mod k_val 7 48 n (n / 48) 37 hn_eq h_period h_rem
    have h_lt : 7 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 7 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 7 := by decide
    exact not_prime_of_dvd_of_lt 7 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 38
    have h_rem : (k_val * 2 ^ 38 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 38 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 38 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 39
    have h_rem : (k_val * 2 ^ 39 + 1) % 5 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 5] := by rfl
    have h_div : 5 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 39 := by omega
      exact k_pow_mod k_val 5 48 n (n / 48) 39 hn_eq h_period h_rem
    have h_lt : 5 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 5 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 5 := by decide
    exact not_prime_of_dvd_of_lt 5 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 40
    have h_rem : (k_val * 2 ^ 40 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 40 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 40 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 41
    have h_rem : (k_val * 2 ^ 41 + 1) % 17 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 17] := by rfl
    have h_div : 17 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 41 := by omega
      exact k_pow_mod k_val 17 48 n (n / 48) 41 hn_eq h_period h_rem
    have h_lt : 17 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 17 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 17 := by decide
    exact not_prime_of_dvd_of_lt 17 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 42
    have h_rem : (k_val * 2 ^ 42 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 42 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 42 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 43
    have h_rem : (k_val * 2 ^ 43 + 1) % 5 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 5] := by rfl
    have h_div : 5 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 43 := by omega
      exact k_pow_mod k_val 5 48 n (n / 48) 43 hn_eq h_period h_rem
    have h_lt : 5 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 5 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 5 := by decide
    exact not_prime_of_dvd_of_lt 5 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 44
    have h_rem : (k_val * 2 ^ 44 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 44 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 44 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 45
    have h_rem : (k_val * 2 ^ 45 + 1) % 673 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 673] := by rfl
    have h_div : 673 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 45 := by omega
      exact k_pow_mod k_val 673 48 n (n / 48) 45 hn_eq h_period h_rem
    have h_lt : 673 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 673 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 673 := by decide
    exact not_prime_of_dvd_of_lt 673 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 46
    have h_rem : (k_val * 2 ^ 46 + 1) % 3 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 3] := by rfl
    have h_div : 3 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 46 := by omega
      exact k_pow_mod k_val 3 48 n (n / 48) 46 hn_eq h_period h_rem
    have h_lt : 3 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 3 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 3 := by decide
    exact not_prime_of_dvd_of_lt 3 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p
  · -- case 47
    have h_rem : (k_val * 2 ^ 47 + 1) % 5 = 0 := by rfl
    have h_period : 2 ^ 48 ≡ 1 [MOD 5] := by rfl
    have h_div : 5 ∣ k_val * 2 ^ n + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hn_eq : n = 48 * (n / 48) + 47 := by omega
      exact k_pow_mod k_val 5 48 n (n / 48) 47 hn_eq h_period h_rem
    have h_lt : 5 < k_val * 2 ^ n + 1 := by
      have h_pow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      generalize 2 ^ n = pow at h_pow ⊢
      have hk : 5 < k_val := by decide
      nlinarith
    have h_prime_p : 1 < 5 := by decide
    exact not_prime_of_dvd_of_lt 5 (k_val * 2 ^ n + 1) h_div h_lt h_prime_p


lemma is_sierpinski_k_val : is_sierpinski_number k_val := by
  dsimp [is_sierpinski_number, k_val]
  refine ⟨by rfl, by decide, ?_⟩
  exact k_not_prime

theorem oeis_270994_conjecture_0.disproof : ¬ (type_of% @oeis_270994_conjecture_0) := by
  intro h
  have hn := h 473165
  rcases hn with ⟨_h1, _h2, h3⟩
  have hk : is_sierpinski_number k_val := is_sierpinski_k_val
  have hk1 : a 473165 < k_val := by
    dsimp [a, k_val]
    omega
  have hk2 : k_val < a 473165 + 28 := by
    dsimp [a, k_val]
    omega
  exact h3 k_val hk hk1 hk2

