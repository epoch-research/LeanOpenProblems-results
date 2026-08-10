import Mathlib
open Finset Nat PowerSeries
open scoped Classical

noncomputable def Yser : ℤ⟦X⟧ := (X:ℤ⟦X⟧)^2 * (invOneSubPow ℤ 1).val

lemma Yser_hasSubst : HasSubst Yser :=
  HasSubst.of_constantCoeff_zero' (by simp [Yser, map_mul, map_pow])

lemma invOneSubPow_one_pow (d : ℕ) : (invOneSubPow ℤ 1)^d = invOneSubPow ℤ d := by
  induction d with
  | zero => simp [invOneSubPow_zero]
  | succ n ih => rw [pow_succ, ih, ← invOneSubPow_add]

lemma invOneSubPow_val_one_pow (d : ℕ) :
    ((invOneSubPow ℤ 1).val)^d = (invOneSubPow ℤ d).val := by
  rw [← Units.val_pow_eq_pow_val, invOneSubPow_one_pow]

lemma Yser_pow (d : ℕ) : Yser^d = (X:ℤ⟦X⟧)^(2*d) * (invOneSubPow ℤ d).val := by
  rw [Yser, mul_pow, ← pow_mul, mul_comm 2 d, invOneSubPow_val_one_pow]

lemma coeff_Yser_pow (d N : ℕ) (h : 2*d ≤ N) :
    (PowerSeries.coeff N) (Yser^d) = (Nat.choose (N - d - 1) (N - 2*d) : ℤ) := by
  rw [Yser_pow, coeff_X_pow_mul', if_pos h]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [invOneSubPow_zero, Units.val_one, Nat.mul_zero, Nat.sub_zero]
    rw [coeff_one]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · rw [if_neg (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp
  · rw [invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℤ d hd, coeff_mk]
    have key : (d - 1 + (N - 2*d)).choose (d-1) = (N-d-1).choose (N-2*d) := by
      rw [show d-1+(N-2*d) = N-d-1 by omega, show N-2*d = (N-d-1)-(d-1) by omega,
          Nat.choose_symm (by omega)]
    exact_mod_cast key

lemma coeff_Yser_pow_zero (d N : ℕ) (h : N < 2*d) :
    (PowerSeries.coeff N) (Yser^d) = 0 := by
  rw [Yser_pow, coeff_X_pow_mul', if_neg (by omega)]

lemma Ring_choose_negNat (N d : ℕ) :
    Ring.choose (-(N:ℤ)) d = (-1)^d * (Nat.choose (N+d-1) d : ℤ) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [Ring.choose_neg, show (N:ℤ)+d-1 = ((N+d-1:ℕ):ℤ) by omega, Ring.choose_natCast,
        Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul]

/-- Lean's definition of `a`. -/
def aLean (n : ℕ) : ℤ :=
  Finset.sum (Finset.range (n / 2 + 1))
    (fun k ↦
      let sign : ℤ := if k % 2 = 0 then 1 else -1
      let term1 : ℕ := (n + k - 1).choose k
      let term2 : ℕ := (n - k - 1).choose (n - 2 * k)
      sign * (term1 : ℤ) * (term2 : ℤ))

lemma sign_eq_negOnePow (d : ℕ) : (if d % 2 = 0 then (1:ℤ) else -1) = (-1)^d := by
  rcases Nat.even_or_odd d with he | ho
  · rw [if_pos (Nat.even_iff.mp he), he.neg_one_pow]
  · rw [if_neg (by have := Nat.odd_iff.mp ho; omega), ho.neg_one_pow]

lemma aLean_eq_coeff (N : ℕ) :
    (aLean N) = (PowerSeries.coeff N) ((binomialSeries ℤ (-(N:ℤ))).subst Yser) := by
  rw [coeff_subst' Yser_hasSubst]
  rw [finsum_eq_finset_sum_of_support_subset _ (s := Finset.range (N/2+1)) ?_]
  · rw [aLean]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_range] at hd
    have h2 : 2 * d ≤ N := by omega
    simp only [binomialSeries_coeff, smul_eq_mul, mul_one]
    rw [coeff_Yser_pow d N h2, Ring_choose_negNat, sign_eq_negOnePow]
  · intro d hd
    simp only [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    push_neg at hcon
    apply hd
    rw [coeff_Yser_pow_zero d N (by omega), smul_zero]
