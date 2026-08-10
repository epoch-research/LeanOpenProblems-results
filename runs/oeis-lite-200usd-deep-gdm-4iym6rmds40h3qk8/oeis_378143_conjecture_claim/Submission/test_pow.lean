import Mathlib

open Nat

theorem not_prime_of_fermat_witness (p : ℕ) (a : ℕ) (ha : a.Coprime p) (hw : a ^ (p - 1) % p ≠ 1) : ¬ Nat.Prime p := by
  intro hp
  have h_eq := Nat.ModEq.pow_card_sub_one_eq_one hp ha
  change a ^ (p - 1) % p = 1 % p at h_eq
  have hp2 : 2 ≤ p := hp.two_le
  have h1 : 1 % p = 1 := Nat.mod_eq_of_lt hp2
  rw [h1] at h_eq
  exact hw h_eq

#eval 3 ^ (10 ^ (2 ^ 3)) % (10 ^ (2 ^ 3) + 1)


#eval (3 : ZMod (10 ^ (2 ^ 4) + 1)) ^ (10 ^ (2 ^ 4))

set_option maxRecDepth 1000000

def val : ZMod (10 ^ (2 ^ 4) + 1) := (3 : ZMod (10 ^ (2 ^ 4) + 1)) ^ (10 ^ (2 ^ 4))

theorem val_eq : val = 7338682844678467 := rfl




