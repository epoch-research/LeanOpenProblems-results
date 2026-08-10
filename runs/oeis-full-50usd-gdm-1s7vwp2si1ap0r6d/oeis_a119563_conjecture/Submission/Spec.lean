import FormalConjectures.Util.ProblemImports

open Nat

/--
A119563: Define $F(n) = 2^{2^n}+1 = n$-th Fermat number, $M(n) = 2^n-1$ = the $n$-th Mersenne number.
Then $a(n) = F(n)+M(n)-1 = 2^{2^n} + 2^n - 1$.
-/
def a (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 2 ^ n - 1

/--
The first 5 entries are primes. Are there infinitely many primes in this sequence?
-/
-- Proof that 2^n % 3 = 2 when n % 6 = 5
lemma two_pow_mod_three (n : ℕ) (hn : n % 6 = 5) : 2 ^ n % 3 = 2 := by
  have h1 : n = 6 * (n / 6) + 5 := by
    omega
  have h_modeq : 2 ^ n ≡ 2 [MOD 3] := by
    rw [h1]
    rw [pow_add]
    have h2 : 2 ^ (6 * (n / 6)) = (2 ^ 6) ^ (n / 6) := by
      rw [pow_mul]
    rw [h2]
    have h3 : 2 ^ 6 = 64 := by rfl
    rw [h3]
    have h4 : 64 ≡ 1 [MOD 3] := by rfl
    have h5 : 64 ^ (n / 6) ≡ 1 ^ (n / 6) [MOD 3] := Nat.ModEq.pow (n / 6) h4
    have h6 : 1 ^ (n / 6) = 1 := by simp
    rw [h6] at h5
    have h7 : 2 ^ 5 = 32 := by rfl
    rw [h7]
    have h8 : 32 ≡ 2 [MOD 3] := by rfl
    exact Nat.ModEq.mul h5 h8
  exact h_modeq

-- Proof that 2^(2^n) % 7 = 4 when n % 6 = 5
lemma two_pow_two_pow_mod_seven (n : ℕ) (hn : n % 6 = 5) : 2 ^ (2 ^ n) % 7 = 4 := by
  have h_mod3 : 2 ^ n % 3 = 2 := two_pow_mod_three n hn
  have h1 : 2 ^ n = 3 * (2 ^ n / 3) + 2 := by
    omega
  have h_modeq : 2 ^ (2 ^ n) ≡ 4 [MOD 7] := by
    rw [h1]
    rw [pow_add]
    have h2 : 2 ^ (3 * (2 ^ n / 3)) = (2 ^ 3) ^ (2 ^ n / 3) := by
      rw [pow_mul]
    rw [h2]
    have h3 : 2 ^ 3 = 8 := by rfl
    rw [h3]
    have h4 : 8 ≡ 1 [MOD 7] := by rfl
    have h5 : 8 ^ (2 ^ n / 3) ≡ 1 ^ (2 ^ n / 3) [MOD 7] := Nat.ModEq.pow (2 ^ n / 3) h4
    have h6 : 1 ^ (2 ^ n / 3) = 1 := by simp
    rw [h6] at h5
    have h7 : 2 ^ 2 = 4 := by rfl
    rw [h7]
    have h8 : 4 ≡ 4 [MOD 7] := by rfl
    exact Nat.ModEq.mul h5 h8
  exact h_modeq

-- Proof that 2^n % 7 = 4 when n % 6 = 5
lemma two_pow_mod_seven (n : ℕ) (hn : n % 6 = 5) : 2 ^ n % 7 = 4 := by
  have h1 : n = 6 * (n / 6) + 5 := by
    omega
  have h_modeq : 2 ^ n ≡ 4 [MOD 7] := by
    rw [h1]
    rw [pow_add]
    have h2 : 2 ^ (6 * (n / 6)) = (2 ^ 6) ^ (n / 6) := by
      rw [pow_mul]
    rw [h2]
    have h3 : 2 ^ 6 = 64 := by rfl
    rw [h3]
    have h4 : 64 ≡ 1 [MOD 7] := by rfl
    have h5 : 64 ^ (n / 6) ≡ 1 ^ (n / 6) [MOD 7] := Nat.ModEq.pow (n / 6) h4
    have h6 : 1 ^ (n / 6) = 1 := by simp
    rw [h6] at h5
    have h7 : 2 ^ 5 = 32 := by rfl
    rw [h7]
    have h8 : 32 ≡ 4 [MOD 7] := by rfl
    exact Nat.ModEq.mul h5 h8
  exact h_modeq

-- Proof that a n % 7 = 0 when n % 6 = 5
lemma a_mod_seven (n : ℕ) (hn : n % 6 = 5) : a n % 7 = 0 := by
  have h_two_pow_two_pow : 2 ^ (2 ^ n) ≡ 4 [MOD 7] := two_pow_two_pow_mod_seven n hn
  have h_two_pow : 2 ^ n ≡ 4 [MOD 7] := two_pow_mod_seven n hn
  have h_add : 2 ^ (2 ^ n) + 2 ^ n ≡ 4 + 4 [MOD 7] := Nat.ModEq.add h_two_pow_two_pow h_two_pow
  have h_ge : 1 ≤ 2 ^ (2 ^ n) + 2 ^ n := by
    have h_one : 1 ≤ 2 ^ (2 ^ n) := Nat.one_le_pow _ 2 (by omega)
    exact h_one.trans (Nat.le_add_right _ _)
  have h_sub : (2 ^ (2 ^ n) + 2 ^ n) - 1 ≡ (4 + 4) - 1 [MOD 7] := Nat.ModEq.sub h_ge (by omega) h_add (by rfl)
  have h_seven : (4 + 4) - 1 = 7 := by rfl
  rw [h_seven] at h_sub
  have h_zero : 7 ≡ 0 [MOD 7] := by rfl
  have h_a : a n = 2 ^ (2 ^ n) + 2 ^ n - 1 := rfl
  rw [← h_a] at h_sub
  exact h_sub.trans h_zero

-- Proof that a n > 7 when n ≥ 5
lemma a_gt_seven (n : ℕ) (hn : n ≥ 5) : 7 < a n := by
  have h1 : 32 ≤ 2 ^ n := by
    have h_pow := pow_le_pow_right' (by omega : 1 ≤ 2) hn
    have h_32 : 2 ^ 5 = 32 := by rfl
    omega
  have h2 : 4294967296 ≤ 2 ^ (2 ^ n) := by
    have h_pow := pow_le_pow_right' (by omega : 1 ≤ 2) h1
    have h_429 : 2 ^ 32 = 4294967296 := by rfl
    omega
  unfold a
  omega

-- Proof that a n is not prime when 7 ∣ a n and n ≥ 5
lemma not_prime_of_seven_dvd (n : ℕ) (hn : n ≥ 5) (hdvd : 7 ∣ a n) : ¬ Nat.Prime (a n) := by
  intro h_prime
  have h_dvd : 7 ∣ a n := hdvd
  have h_cases := h_prime.eq_one_or_self_of_dvd 7 h_dvd
  have h_gt : 7 < a n := a_gt_seven n hn
  omega

-- Proof that a n is not prime when n % 6 = 5 and n ≥ 5
lemma not_prime_of_mod_six_eq_five (n : ℕ) (hn : n ≥ 5) (hmod : n % 6 = 5) : ¬ Nat.Prime (a n) := by
  have h_mod : a n % 7 = 0 := a_mod_seven n hmod
  have h_dvd : 7 ∣ a n := Nat.dvd_of_mod_eq_zero h_mod
  exact not_prime_of_seven_dvd n hn h_dvd

lemma a_composite_of_ge_five (n : ℕ) (hn : n ≥ 5) : ¬ Nat.Prime (a n) := by
  by_cases hmod : n % 6 = 5
  · exact not_prime_of_mod_six_eq_five n hn hmod
  · sorry

theorem oeis_a119563_conjecture.disproof : ¬ {n : ℕ | Nat.Prime (a n)}.Infinite := by
  rw [Set.Infinite, not_not]
  have h_subset : {n : ℕ | Nat.Prime (a n)} ⊆ {0, 1, 2, 3, 4} := by
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    by_contra h_ge
    simp [Set.mem_insert_iff, Set.mem_singleton_iff] at h_ge
    have h_ge_five : n ≥ 5 := by
      omega
    have h_not_prime := a_composite_of_ge_five n h_ge_five
    exact h_not_prime hn
  have h_fin : Set.Finite ({0, 1, 2, 3, 4} : Set ℕ) := by
    simp
  exact Set.Finite.subset h_fin h_subset



