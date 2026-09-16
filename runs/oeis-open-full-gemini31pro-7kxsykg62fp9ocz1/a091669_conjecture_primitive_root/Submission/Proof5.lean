import Mathlib
import Submission.Spec

open Nat BigOperators

lemma mod_div_trick (p k : ℕ) (hp : p ≥ 2) (hk : k ≥ 2) :
  (p * k - 1) % p = p - 1 ∧ (p * k - 1) / p = k - 1 := by
  have h1 : p * k - 1 = (p - 1) + p * (k - 1) := by
    zify [show p * k ≥ 1 by nlinarith, show k ≥ 1 by omega, show p ≥ 1 by omega]
    ring
  have hl : p - 1 < p := by omega
  constructor
  · rw [h1]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  · rw [h1]
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hl]
    omega
