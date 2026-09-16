import Mathlib

open Nat

lemma mod_div_identity (A B C c : ℕ) (hc : 0 < c) :
  (A + B + C) / c = A / c + B / c + C / c + (A % c + B % c + C % c) / c := by
  have h_add : (c * (A / c + B / c + C / c) + (A % c + B % c + C % c)) / c = (A % c + B % c + C % c) / c + (A / c + B / c + C / c) := by
    rw [Nat.add_comm (c * _), Nat.add_mul_div_left _ _ hc]
  have hS : A + B + C = c * (A / c + B / c + C / c) + (A % c + B % c + C % c) := by
    have h1 : A = c * (A / c) + A % c := (Nat.div_add_mod A c).symm
    have h2 : B = c * (B / c) + B % c := (Nat.div_add_mod B c).symm
    have h3 : C = c * (C / c) + C % c := (Nat.div_add_mod C c).symm
    calc
      A + B + C = (c * (A / c) + A % c) + B + C := by nth_rw 1 [h1]
      _ = (c * (A / c) + A % c) + (c * (B / c) + B % c) + C := by nth_rw 1 [h2]
      _ = (c * (A / c) + A % c) + (c * (B / c) + B % c) + (c * (C / c) + C % c) := by nth_rw 1 [h3]
      _ = c * (A / c + B / c + C / c) + (A % c + B % c + C % c) := by ring
  rw [hS, h_add]
  exact Nat.add_comm _ _

lemma f_eq (k c : ℕ) (hc : 0 < c) :
  (6 * k) / c - (3 * k) / c - (2 * k) / c - k / c = ((3 * k) % c + (2 * k) % c + k % c) / c := by
  have h1 : 3 * k + 2 * k + k = 6 * k := by omega
  have h2 := mod_div_identity (3 * k) (2 * k) k c hc
  rw [h1] at h2
  have h3 : (6 * k) / c - (3 * k) / c - (2 * k) / c - k / c = (6 * k) / c - ((3 * k) / c + (2 * k) / c + k / c) := by omega
  rw [h3, h2]
  exact Nat.add_sub_cancel_left _ _

lemma mod_div_identity_2 (A B c : ℕ) (hc : 0 < c) :
  (A + B) / c = A / c + B / c + (A % c + B % c) / c := by
  have h_add : (c * (A / c + B / c) + (A % c + B % c)) / c = (A % c + B % c) / c + (A / c + B / c) := by
    rw [Nat.add_comm (c * _), Nat.add_mul_div_left _ _ hc]
  have hS : A + B = c * (A / c + B / c) + (A % c + B % c) := by
    have h1 : A = c * (A / c) + A % c := (Nat.div_add_mod A c).symm
    have h2 : B = c * (B / c) + B % c := (Nat.div_add_mod B c).symm
    calc
      A + B = (c * (A / c) + A % c) + B := by nth_rw 1 [h1]
      _ = (c * (A / c) + A % c) + (c * (B / c) + B % c) := by nth_rw 1 [h2]
      _ = c * (A / c + B / c) + (A % c + B % c) := by ring
  rw [hS, h_add]
  exact Nat.add_comm _ _

lemma g_eq (n c : ℕ) (hc : 0 < c) :
  (3 * n) / c - (2 * n) / c - n / c = ((2 * n) % c + n % c) / c := by
  have h1 : 2 * n + n = 3 * n := by omega
  have h2 := mod_div_identity_2 (2 * n) n c hc
  rw [h1] at h2
  have h3 : (3 * n) / c - (2 * n) / c - n / c = (3 * n) / c - ((2 * n) / c + n / c) := by omega
  rw [h3, h2]
  exact Nat.add_sub_cancel_left _ _

