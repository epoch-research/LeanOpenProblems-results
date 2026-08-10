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

-- n = 18, factor 639631361
theorem test_18 : powModFuel 19 10 (2 ^ 18) 639631361 = 639631360 := by decide

-- n = 19, factor 70254593
theorem test_19 : powModFuel 20 10 (2 ^ 19) 70254593 = 70254592 := by decide

-- n = 20, factor 167772161
theorem test_20 : powModFuel 21 10 (2 ^ 20) 167772161 = 167772160 := by decide

-- n = 22, factor 101702694862849
theorem test_22 : powModFuel 23 10 (2 ^ 22) 101702694862849 = 101702694862848 := by decide
