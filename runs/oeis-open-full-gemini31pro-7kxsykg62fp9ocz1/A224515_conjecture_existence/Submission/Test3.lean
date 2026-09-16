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

lemma F_mod (k L : ℕ) (hL : 2 ≤ L) :
  ( (k + 2^L)^2 ^^^ (k + 1 + 2^L)^2 ) % 2^(L+2) =
  ( (k^2 ^^^ (k+1)^2) + 2^(L+1) ) % 2^(L+2) := by
  have h1 : (k + 2^L)^2 % 2^(L+2) = (k^2 + (k % 2) * 2^(L+1)) % 2^(L+2) := sq_add_two_pow_mod k L hL
  have h2 : (k + 1 + 2^L)^2 % 2^(L+2) = ((k + 1)^2 + ((k + 1) % 2) * 2^(L+1)) % 2^(L+2) := sq_add_two_pow_mod (k + 1) L hL
  rw [Nat.xor_mod_two_pow, h1, h2, ←Nat.xor_mod_two_pow]
  have hcases : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hcases with hk0 | hk1
  · have hk1_mod : (k + 1) % 2 = 1 := by omega
    rw [hk0, hk1_mod]
    have : k^2 + 0 * 2^(L+1) = k^2 := by ring
    rw [this]
    have : (k+1)^2 + 1 * 2^(L+1) = (k+1)^2 + 2^(L+1) := by ring
    rw [this]
    exact xor_add_two_pow_mod (k^2) ((k+1)^2) (L+1)
  · have hk0_mod : (k + 1) % 2 = 0 := by omega
    rw [hk1, hk0_mod]
    have : (k+1)^2 + 0 * 2^(L+1) = (k+1)^2 := by ring
    rw [this]
    have : k^2 + 1 * 2^(L+1) = k^2 + 2^(L+1) := by ring
    rw [this]
    have hcomm : (k^2 + 2^(L+1)) ^^^ (k+1)^2 = (k+1)^2 ^^^ (k^2 + 2^(L+1)) := Nat.xor_comm _ _
    rw [hcomm]
    have h_lemma := xor_add_two_pow_mod ((k+1)^2) (k^2) (L+1)
    rw [h_lemma]
    have hcomm2 : (k+1)^2 ^^^ k^2 = k^2 ^^^ (k+1)^2 := Nat.xor_comm _ _
    rw [hcomm2]
