import Mathlib
open Nat

lemma bit_false_two_pow (L : ℕ) : 2^(L+1) = bit false (2^L) := by
  rw [Nat.pow_succ', Nat.bit_false]

lemma bit_add_my (b : Bool) (m n : ℕ) : bit b (m + n) = bit b m + 2 * n := by
  rw [Nat.bit_val, Nat.bit_val]
  omega

lemma xor_two_pow_add (L : ℕ) : ∀ C, C < 2^L → C ^^^ 2^L = C + 2^L := by
  induction' L with L ih
  · intro C h
    have : C = 0 := by omega
    rw [this]
    rfl
  · intro C h
    have h1 : C.div2 < 2^L := by
      rw [Nat.div2_val]
      omega
    have eqC : bit C.bodd C.div2 = C := Nat.bit_bodd_div2 C
    calc C ^^^ 2^(L+1)
      _ = bit C.bodd C.div2 ^^^ 2^(L+1) := by nth_rw 1 [←eqC]
      _ = bit C.bodd C.div2 ^^^ bit false (2^L) := by rw [bit_false_two_pow L]
      _ = bit (C.bodd != false) (C.div2 ^^^ 2^L) := by rw [Nat.xor_bit]
      _ = bit C.bodd (C.div2 + 2^L) := by 
          have : (C.bodd != false) = C.bodd := by cases C.bodd <;> rfl
          rw [this, ih _ h1]
      _ = bit C.bodd C.div2 + 2 * 2^L := bit_add_my _ _ _
      _ = C + 2^(L+1) := by rw [eqC, ←Nat.pow_succ']

lemma add_xor_two_pow (L C : ℕ) (h : C < 2^L) : (C + 2^L) ^^^ 2^L = C := by
  have : C + 2^L = C ^^^ 2^L := (xor_two_pow_add L C h).symm
  rw [this]
  exact Nat.xor_xor_cancel_right C (2^L)

lemma add_two_pow_mod_eq_xor (Y L : ℕ) :
  (Y + 2^L) % 2^(L+1) = (Y % 2^(L+1)) ^^^ 2^L := by
  have hM : Y % 2^(L+1) < 2^(L+1) := Nat.mod_lt _ (by positivity)
  rcases lt_or_ge (Y % 2^(L+1)) (2^L) with h1 | h1
  · have eq1 : (Y % 2^(L+1)) ^^^ 2^L = (Y % 2^(L+1)) + 2^L := xor_two_pow_add L _ h1
    rw [eq1]
    rw [←Nat.mod_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  · have eq1 : Y % 2^(L+1) = (Y % 2^(L+1) - 2^L) + 2^L := by omega
    have hC : Y % 2^(L+1) - 2^L < 2^L := by omega
    have eq2 : (Y % 2^(L+1)) ^^^ 2^L = Y % 2^(L+1) - 2^L := by
      nth_rw 1 [eq1]
      rw [add_xor_two_pow L _ hC]
    rw [eq2]
    rw [←Nat.mod_add_mod]
    have eq3 : Y % 2^(L+1) + 2^L = (Y % 2^(L+1) - 2^L) + 2^(L+1) := by
      have : 2^(L+1) = 2^L + 2^L := by
        have : 2^(L+1) = 2 * 2^L := by rw [Nat.pow_succ']
        omega
      omega
    rw [eq3, Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)

lemma xor_add_two_pow_mod (X Y L : ℕ) :
  (X ^^^ (Y + 2^L)) % 2^(L+1) = ((X ^^^ Y) + 2^L) % 2^(L+1) := by
  have h1 : (X ^^^ (Y + 2^L)) % 2^(L+1) = X % 2^(L+1) ^^^ (Y + 2^L) % 2^(L+1) := Nat.xor_mod_two_pow
  rw [h1]
  rw [add_two_pow_mod_eq_xor]
  rw [←Nat.xor_assoc]
  have h2 : X % 2^(L+1) ^^^ Y % 2^(L+1) = (X ^^^ Y) % 2^(L+1) := Nat.xor_mod_two_pow.symm
  rw [h2]
  rw [←add_two_pow_mod_eq_xor]
