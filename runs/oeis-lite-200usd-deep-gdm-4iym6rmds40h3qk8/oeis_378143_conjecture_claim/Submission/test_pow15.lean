import Mathlib

open Nat

def powModFuel (fuel : ℕ) (base exp mod : ℕ) : ℕ :=
  match fuel with
  | 0 => 1 % mod
  | fuel + 1 =>
    if exp = 0 then
      1 % mod
    else
      let half := powModFuel fuel base (exp / 2) mod
      if exp % 2 = 0 then
        (half * half) % mod
      else
        (half * half % mod * (base % mod)) % mod

theorem powModFuel_eq_pow_mod (fuel : ℕ) (base exp mod : ℕ) (h_fuel : exp < 2 ^ fuel) :
  powModFuel fuel base exp mod = base ^ exp % mod := by
  induction fuel generalizing exp with
  | zero =>
    have h_exp : exp = 0 := by omega
    rw [h_exp]
    rfl
  | succ fuel ih =>
    by_cases h_exp : exp = 0
    · rw [h_exp]
      rfl
    · unfold powModFuel
      split_ifs with h_even
      · -- exp % 2 = 0
        have h_lt : exp / 2 < 2 ^ fuel := by
          have h1 : exp / 2 * 2 ≤ exp := Nat.div_mul_le_self exp 2
          omega
        rw [ih (exp / 2) h_lt]
        rw [← Nat.mul_mod]
        rw [← Nat.pow_add]
        congr 1
        have h_eq : exp / 2 + exp / 2 = exp := by
          have h_div := Nat.div_add_mod exp 2
          rw [h_even] at h_div
          omega
        rw [h_eq]
      · -- exp % 2 ≠ 0
        have h_lt : exp / 2 < 2 ^ fuel := by
          have h1 : exp / 2 * 2 ≤ exp := Nat.div_mul_le_self exp 2
          omega
        rw [ih (exp / 2) h_lt]
        rw [← Nat.mul_mod]
        have mod_mul_mod_mul (a b c m : ℕ) : (a % m * (b % m) * c) % m = (a * b * c) % m := by
          have h1 : a % m ≡ a [MOD m] := Nat.mod_mod a m
          have h2 : b % m ≡ b [MOD m] := Nat.mod_mod b m
          have h3 : c ≡ c [MOD m] := rfl
          have h4 := Nat.ModEq.mul h1 h2
          have h5 := Nat.ModEq.mul h4 h3
          exact h5
        rw [mod_mul_mod_mul]
        rw [← Nat.pow_add]
        congr 1
        have h_odd : exp % 2 = 1 := by omega
        have h_eq : exp / 2 + exp / 2 + 1 = exp := by
          have h_div := Nat.div_add_mod exp 2
          rw [h_odd] at h_div
          omega
        have h_pow_succ : base ^ (exp / 2 + exp / 2) * base = base ^ (exp / 2 + exp / 2 + 1) := by
          rw [Nat.pow_succ]
        rw [h_pow_succ]
        rw [h_eq]

theorem test_15 : powModFuel 16 10 (2 ^ 15) 65537 = 65536 := by decide

theorem test_16 : powModFuel 17 10 (2 ^ 16) 8257537 = 8257536 := by decide

theorem test_17 : powModFuel 18 10 (2 ^ 17) 175636481 = 175636480 := by decide

theorem div_15 : 65537 ∣ 10 ^ (2 ^ 15) + 1 := by
  have h_mod : 10 ^ (2 ^ 15) % 65537 = 65536 := by
    have h_eq := powModFuel_eq_pow_mod 16 10 (2 ^ 15) 65537 (by decide)
    rw [← h_eq]
    rfl
  have h_dvd : (10 ^ (2 ^ 15) + 1) % 65537 = 0 := by
    rw [Nat.add_mod, h_mod]
  exact Nat.dvd_of_mod_eq_zero h_dvd

