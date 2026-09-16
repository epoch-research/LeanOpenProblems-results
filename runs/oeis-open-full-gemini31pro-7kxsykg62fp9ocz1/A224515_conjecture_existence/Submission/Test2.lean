import Mathlib
open Nat

lemma k_mul_two_pow_mod (k L : ℕ) :
  (k * 2^(L+1)) % 2^(L+2) = (k % 2) * 2^(L+1) := by
  have : k = 2 * (k / 2) + k % 2 := by omega
  nth_rw 1 [this]
  have h2 : (2 * (k / 2) + k % 2) * 2^(L+1) = (k / 2) * 2^(L+2) + (k % 2) * 2^(L+1) := by
    have h2a : 2^(L+2) = 2 * 2^(L+1) := by rw [Nat.pow_succ']
    rw [h2a]
    ring
  rw [h2]
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod, zero_add, Nat.mod_mod]
  have h3 : (k % 2) * 2^(L+1) < 2^(L+2) := by
    have : k % 2 < 2 := Nat.mod_lt k (by positivity)
    have h4 : 2^(L+2) = 2 * 2^(L+1) := by rw [Nat.pow_succ']
    rw [h4]
    have hpos : 0 < 2^(L+1) := by positivity
    nlinarith
  exact Nat.mod_eq_of_lt h3

lemma sq_add_two_pow_eq (k L : ℕ) :
  (k + 2^L)^2 = k^2 + k * 2^(L+1) + 2^(2*L) := by
  have h1 : 2^(L+1) = 2 * 2^L := by rw [Nat.pow_succ', Nat.mul_comm]
  have h2 : 2^(2*L) = (2^L)^2 := by rw [←Nat.pow_mul, Nat.mul_comm]
  rw [h1, h2]
  ring

lemma sq_add_two_pow_mod (k L : ℕ) (hL : 2 ≤ L) :
  (k + 2^L)^2 % 2^(L+2) = (k^2 + (k % 2) * 2^(L+1)) % 2^(L+2) := by
  rw [sq_add_two_pow_eq]
  have h3 : 2^(2*L) = 2^(2*L - (L+2)) * 2^(L+2) := by
    rw [←Nat.pow_add]
    congr 1
    omega
  rw [h3]
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod, add_zero, Nat.mod_mod]
  have h4 : (k^2 + k * 2^(L+1)) % 2^(L+2) = (k^2 % 2^(L+2) + (k * 2^(L+1)) % 2^(L+2)) % 2^(L+2) := by
    rw [Nat.add_mod]
  have h5 : (k^2 + (k % 2) * 2^(L+1)) % 2^(L+2) = (k^2 % 2^(L+2) + ((k % 2) * 2^(L+1)) % 2^(L+2)) % 2^(L+2) := by
    rw [Nat.add_mod]
  rw [h4, h5, k_mul_two_pow_mod]
  have h6 : ((k % 2) * 2^(L+1)) % 2^(L+2) = (k % 2) * 2^(L+1) := by
    have : k % 2 < 2 := Nat.mod_lt k (by positivity)
    have h4 : 2^(L+2) = 2 * 2^(L+1) := by rw [Nat.pow_succ']
    rw [h4]
    have hpos : 0 < 2^(L+1) := by positivity
    have : (k % 2) * 2^(L+1) < 2 * 2^(L+1) := by nlinarith
    exact Nat.mod_eq_of_lt this
  rw [h6]
