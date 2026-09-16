import Mathlib

lemma fermat (p : ℕ) [hp : Fact p.Prime] (hodd : p > 2) (j : ℕ) :
  p ∣ 2 ^ (j * (p - 1)) - 1 := by
  have h_ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h1 : ((2 : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by
      calc ((2 : ℕ) : ZMod p) = (2 : ZMod p) := by rfl
        _ = (0 : ZMod p) := h
        _ = ((0 : ℕ) : ZMod p) := Nat.cast_zero.symm
    have h2 : 2 ≡ 0 [MOD p] := (ZMod.natCast_eq_natCast_iff 2 0 p).mp h1
    have h3 : p ∣ 2 := Nat.modEq_zero_iff_dvd.mp h2
    have : p ≤ 2 := Nat.le_of_dvd (by decide) h3
    omega
  have h1 : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h_ne
  have h2 : (2 : ZMod p) ^ (j * (p - 1)) = 1 := by
    rw [mul_comm, pow_mul, h1, one_pow]
  have h3 : ((2 ^ (j * (p - 1)) : ℕ) : ZMod p) = 1 := by
    rw [Nat.cast_pow]
    exact h2
  have h4 : ((2 ^ (j * (p - 1)) - 1 : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by
    have h_pow : 2 ^ (j * (p - 1)) ≥ 1 := Nat.one_le_two_pow
    rw [Nat.cast_sub h_pow, h3, Nat.cast_one, sub_self, Nat.cast_zero]
  have h5 : 2 ^ (j * (p - 1)) - 1 ≡ 0 [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ p).mp h4
  exact Nat.modEq_zero_iff_dvd.mp h5
