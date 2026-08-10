import Mathlib

open Nat

lemma test_coprime_decide (q e f : ℕ) (h_zmod : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2) 
    (hq_mod : q % 9 = 1) (he : 3 ≤ e) : False := by
  have hq_cast : (q : ZMod 9) = 1 := by
    have : ((q : ℕ) : ZMod 9) = ((q % 9 : ℕ) : ZMod 9) := by rw [ZMod.natCast_mod]
    rw [this, hq_mod]
    rfl
  have h3e : (3 : ZMod 9) ^ e = 0 := by
    have he_eq : e = (e - 2) + 2 := by omega
    rw [he_eq, pow_add]
    have : (3 : ZMod 9) ^ 2 = 0 := rfl
    rw [this, mul_zero]
  rw [hq_cast, one_pow, h3e, sub_zero] at h_zmod
  revert h_zmod
  decide







