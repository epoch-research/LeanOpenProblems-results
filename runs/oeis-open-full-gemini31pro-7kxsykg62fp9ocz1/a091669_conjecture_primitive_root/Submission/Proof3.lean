import Mathlib

open Nat

lemma digits_sum_pos (p n : ℕ) (hp : p > 1) (hn : n > 0) :
  (p.digits n).sum ≥ 1 := by
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.digits_def' hp hn]
  simp only [List.sum_cons]
  by_cases h0 : n / p = 0
  · have h_mod : n % p = n := Nat.mod_eq_of_lt (Nat.div_eq_zero_iff (by omega).mp h0)
    omega
  · have h_div_pos : n / p > 0 := by omega
    have h_lt : n / p < n := Nat.div_lt_self hn hp
    have := ih (n / p) h_lt h_div_pos
    omega
