import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option linter.unusedTactic false

open Nat

def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)

-- Disproof helper definitions and lemmas

def k0 : ℕ := 5292270077783

def covering_prime_disproof (m : ℕ) : ℕ :=
  if m % 2 = 0 then 3
  else if m % 8 = 1 then 17
  else if m % 16 = 5 then 257
  else if m % 3 = 1 then 7
  else if m % 48 = 29 then 97
  else if m % 48 = 45 then 673
  else 5

theorem covering_prime_disproof_prime (m : ℕ) : Nat.Prime (covering_prime_disproof m) := by
  dsimp [covering_prime_disproof]
  split_ifs <;> decide

theorem covering_prime_disproof_eq (m : ℕ) (r : ℕ) (h : m % 48 = r) :
  covering_prime_disproof m = covering_prime_disproof r := by
  have h2 : m % 2 = r % 2 := by omega
  have h8 : m % 8 = r % 8 := by omega
  have h16 : m % 16 = r % 16 := by omega
  have h3 : m % 3 = r % 3 := by omega
  have h48 : m % 48 = r % 48 := by omega
  dsimp [covering_prime_disproof]
  rw [h2, h8, h16, h3, h48]

theorem pow_two_mod_48_helper (p : ℕ) (hp : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 ∨ p = 97 ∨ p = 257 ∨ p = 673) :
  ModEq p (2^48) 1 := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem pow_two_mod_48 (m : ℕ) (p : ℕ) (hp : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 ∨ p = 97 ∨ p = 257 ∨ p = 673) :
  ModEq p (2^m) (2^(m % 48)) := by
  have h_div := div_add_mod m 48
  have h1 : 2^m = 2^(48 * (m / 48) + m % 48) := by rw [h_div]
  rw [h1]
  rw [pow_add]
  rw [pow_mul]
  have h_base : ModEq p (2^48) 1 := pow_two_mod_48_helper p hp
  have h_pow : ModEq p ((2^48)^(m / 48)) (1^(m / 48)) := ModEq.pow (m / 48) h_base
  have h_pow_one : (1^(m / 48)) = 1 := by simp
  rw [h_pow_one] at h_pow
  have h_mul : ModEq p ((2^48)^(m / 48) * 2^(m % 48)) (1 * 2^(m % 48)) := ModEq.mul_right (2^(m % 48)) h_pow
  rw [one_mul] at h_mul
  exact h_mul

theorem covering_prime_disproof_dvd_helper : ∀ r : ℕ, r < 48 → ModEq (covering_prime_disproof r) (k0 * 2^r + 1) 0 := by
  decide

theorem covering_prime_disproof_dvd (m : ℕ) : ModEq (covering_prime_disproof m) (k0 * 2^m + 1) 0 := by
  have h_prop : covering_prime_disproof m = 3 ∨ covering_prime_disproof m = 5 ∨ covering_prime_disproof m = 7 ∨ covering_prime_disproof m = 17 ∨ covering_prime_disproof m = 97 ∨ covering_prime_disproof m = 257 ∨ covering_prime_disproof m = 673 := by
    dsimp [covering_prime_disproof]
    split_ifs <;> simp
  have h_pow := pow_two_mod_48 m (covering_prime_disproof m) h_prop
  have h_mul : ModEq (covering_prime_disproof m) (k0 * 2^m) (k0 * 2^(m % 48)) := ModEq.mul_left k0 h_pow
  have h_add : ModEq (covering_prime_disproof m) (k0 * 2^m + 1) (k0 * 2^(m % 48) + 1) := ModEq.add_right 1 h_mul
  have h_eq : covering_prime_disproof m = covering_prime_disproof (m % 48) := covering_prime_disproof_eq m (m % 48) rfl
  have h_add_rw := h_add
  rw [h_eq] at h_add_rw
  have h_helper := covering_prime_disproof_dvd_helper (m % 48) (Nat.mod_lt m (by decide))
  have h_trans := ModEq.trans h_add_rw h_helper
  rw [h_eq]
  exact h_trans

theorem is_sierpinski_number_k0 : is_sierpinski_number k0 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · intro m hm hp
    have h_dvd : covering_prime_disproof m ∣ k0 * 2^m + 1 := Nat.dvd_of_mod_eq_zero (covering_prime_disproof_dvd m)
    have h_eq : covering_prime_disproof m = k0 * 2^m + 1 := by
      have h_prime : Nat.Prime (covering_prime_disproof m) := covering_prime_disproof_prime m
      rcases hp.eq_one_or_self_of_dvd _ h_dvd with h_one | h_self
      · exfalso
        have : covering_prime_disproof m ≠ 1 := h_prime.ne_one
        exact this h_one
      · exact h_self
    have h_lt : covering_prime_disproof m < k0 * 2^m + 1 := by
      have h_max : covering_prime_disproof m ≤ 673 := by
        dsimp [covering_prime_disproof]
        split_ifs <;> omega
      have h_min : k0 * 2^m + 1 ≥ 5292270077783 * 2 + 1 := by
        dsimp [k0]
        have h_m_ge : m ≥ 1 := hm
        have h2 : 2^1 ≤ 2^m := Nat.pow_le_pow_right (by decide) h_m_ge
        nlinarith
      omega
    omega

theorem oeis_270994_conjecture_0.disproof : ¬ (∀ n : ℕ,
  is_sierpinski_number (a n) ∧
  is_sierpinski_number (a n + 28) ∧
  (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False)) := by
  intro h
  have h_n0 := h 473165
  rcases h_n0 with ⟨_, _, h_no_between⟩
  apply h_no_between k0
  · exact is_sierpinski_number_k0
  · dsimp [a, k0]
    decide
  · dsimp [a, k0]
    decide
