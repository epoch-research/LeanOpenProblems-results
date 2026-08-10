import Mathlib

open Nat

set_option exponentiation.threshold 100000
set_option maxRecDepth 200000


def powMod (base exp mod : ℕ) : ℕ :=
  if h : exp = 0 then
    1 % mod
  else
    have : exp / 2 < exp := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
    let half := powMod base (exp / 2) mod
    if exp % 2 = 0 then
      (half * half) % mod
    else
      (half * half % mod * (base % mod)) % mod
termination_by exp

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

theorem test_fuel_13 : powModFuel 100 3 (10 ^ (2 ^ 3)) (10 ^ (2 ^ 3) + 1) ≠ 1 := by decide

theorem test_fuel_real_13 : powModFuel 30000 3 (10 ^ (2 ^ 13)) (10 ^ (2 ^ 13) + 1) ≠ 1 := by decide




theorem mod_mul_mod_mul (a b c m : ℕ) : (a % m * (b % m) * c) % m = (a * b * c) % m := by
  have h1 : a % m ≡ a [MOD m] := Nat.mod_mod a m
  have h2 : b % m ≡ b [MOD m] := Nat.mod_mod b m
  have h3 : c ≡ c [MOD m] := rfl
  have h4 := Nat.ModEq.mul h1 h2
  have h5 := Nat.ModEq.mul h4 h3
  exact h5


theorem powMod_eq_pow_mod (base exp mod : ℕ) : powMod base exp mod = base ^ exp % mod := by
  induction exp using powMod.induct base mod with
  | case1 =>
    unfold powMod
    simp
  | case2 x hx hdiv heven ih =>
    unfold powMod
    rw [dif_neg hx]
    rw [if_pos heven]
    rw [ih]
    -- Goal: (base ^ (x / 2) % mod * (base ^ (x / 2) % mod)) % mod = base ^ x % mod
    rw [← Nat.mul_mod]
    rw [← Nat.pow_add]
    -- Goal: base ^ (x / 2 + x / 2) % mod = base ^ x % mod
    -- Since x % 2 = 0, x = x / 2 + x / 2
    have hx_half : x / 2 + x / 2 = x := by
      have h1 : 2 * (x / 2) + x % 2 = x := Nat.div_add_mod x 2
      rw [heven] at h1
      have h2 : 2 * (x / 2) = x / 2 + x / 2 := by ring
      omega
    rw [hx_half]
  | case3 x hx hdiv hodd ih =>
    unfold powMod
    rw [dif_neg hx]
    rw [if_neg hodd]
    rw [ih]
    -- Goal: ((base ^ (x / 2) % mod * (base ^ (x / 2) % mod)) % mod * (base % mod)) % mod = base ^ x % mod
    -- Let's rewrite the outer multiplication using ← Nat.mul_mod:
    -- wait, we want to rewrite: (A % mod * (base % mod)) % mod to (A * base) % mod
    -- where A = (base ^ (x / 2) % mod * (base ^ (x / 2) % mod))
    -- But in the goal, we have: (half * half % mod * (base % mod)) % mod
    -- which is ( (half * half % mod) * (base % mod) ) % mod
    -- This matches ← Nat.mul_mod!
    rw [← Nat.mul_mod]
    -- This gives: (base ^ (x / 2) % mod * (base ^ (x / 2) % mod) * base) % mod = base ^ x % mod
    -- Now we want to rewrite the first part: base ^ (x / 2) % mod * (base ^ (x / 2) % mod)
    -- wait, we can't do ← Nat.mul_mod directly because there is no % mod around it.
    -- But we can rewrite: (X % mod * (Y % mod) * base) % mod = (X * Y * base) % mod
    rw [mod_mul_mod_mul]
    rw [← Nat.pow_add]
    -- Goal: base ^ (x / 2 + x / 2) * base % mod = base ^ x % mod
    -- Since x % 2 ≠ 0, x % 2 = 1.
    have hodd_val : x % 2 = 1 := by omega
    have hx_half : x / 2 + x / 2 + 1 = x := by
      have h1 : 2 * (x / 2) + x % 2 = x := Nat.div_add_mod x 2
      rw [hodd_val] at h1
      have h2 : 2 * (x / 2) = x / 2 + x / 2 := by ring
      omega
    -- base ^ (x / 2 + x / 2) * base = base ^ (x / 2 + x / 2 + 1)
    have h_pow_succ : base ^ (x / 2 + x / 2) * base = base ^ (x / 2 + x / 2 + 1) := by
      rw [Nat.pow_succ]
    rw [h_pow_succ]
    rw [hx_half]




#check Nat.mul_mod
#check Nat.pow_add
#check Nat.div_add_mod



