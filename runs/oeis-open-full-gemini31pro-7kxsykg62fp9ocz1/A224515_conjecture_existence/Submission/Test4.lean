import Mathlib
open Nat

lemma sq_mod_eight (x : ℕ) : x^2 % 8 = (x % 4)^2 % 8 := by
  have : x = 4 * (x / 4) + x % 4 := by omega
  nth_rw 1 [this]
  have h1 : (4 * (x / 4) + x % 4)^2 = 16 * (x / 4)^2 + 8 * (x / 4) * (x % 4) + (x % 4)^2 := by ring
  rw [h1]
  have : 16 * (x / 4)^2 + 8 * (x / 4) * (x % 4) + (x % 4)^2 = 8 * (2 * (x / 4)^2 + (x / 4) * (x % 4)) + (x % 4)^2 := by ring
  rw [this, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod, zero_add, Nat.mod_mod]

lemma F_mod_1 (k : ℕ) :
  ( (k + 2)^2 ^^^ (k + 3)^2 ) % 8 =
  ( (k^2 ^^^ (k+1)^2) + 4 ) % 8 := by
  have h1 : (k + 2)^2 % 8 = (k % 4 + 2)^2 % 8 := by
    have h_mod : (k + 2) % 4 = (k % 4 + 2) % 4 := by omega
    rw [sq_mod_eight (k+2), h_mod, ←sq_mod_eight (k % 4 + 2)]
  have h2 : (k + 3)^2 % 8 = (k % 4 + 3)^2 % 8 := by
    have h_mod : (k + 3) % 4 = (k % 4 + 3) % 4 := by omega
    rw [sq_mod_eight (k+3), h_mod, ←sq_mod_eight (k % 4 + 3)]
  have h3 : k^2 % 8 = (k % 4)^2 % 8 := sq_mod_eight k
  have h4 : (k + 1)^2 % 8 = (k % 4 + 1)^2 % 8 := by
    have h_mod : (k + 1) % 4 = (k % 4 + 1) % 4 := by omega
    rw [sq_mod_eight (k+1), h_mod, ←sq_mod_eight (k % 4 + 1)]
  
  have H : ( (k + 2)^2 ^^^ (k + 3)^2 ) % 8 = ( (k % 4 + 2)^2 ^^^ (k % 4 + 3)^2 ) % 8 := by
    have h8 : 8 = 2^3 := by rfl
    rw [h8, Nat.xor_mod_two_pow]
    have h1' : (k + 2)^2 % 2^3 = (k % 4 + 2)^2 % 2^3 := h1
    have h2' : (k + 3)^2 % 2^3 = (k % 4 + 3)^2 % 2^3 := h2
    rw [h1', h2', ←Nat.xor_mod_two_pow]
  have H2 : ( (k^2 ^^^ (k+1)^2) + 4 ) % 8 = ( ((k % 4)^2 ^^^ (k % 4 + 1)^2) + 4 ) % 8 := by
    have h8 : 8 = 2^3 := by rfl
    have heq : (k^2 ^^^ (k+1)^2) % 8 = ((k % 4)^2 ^^^ (k % 4 + 1)^2) % 8 := by
      rw [h8, Nat.xor_mod_two_pow]
      have h3' : k^2 % 2^3 = (k % 4)^2 % 2^3 := h3
      have h4' : (k+1)^2 % 2^3 = (k % 4 + 1)^2 % 2^3 := h4
      rw [h3', h4', ←Nat.xor_mod_two_pow]
    rw [Nat.add_mod, heq, ←Nat.add_mod]

  rw [H, H2]
  have h_mod : k % 4 < 4 := Nat.mod_lt k (by decide)
  interval_cases m : (k % 4)
  · rfl
  · rfl
  · rfl
  · rfl
