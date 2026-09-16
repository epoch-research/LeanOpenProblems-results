import Mathlib
import Submission.Spec
import Submission.Proof20

open Nat BigOperators

lemma P_mod_n_eq_one (n : ℕ) (hn_prime : n.Prime) (hn2 : n > 2)
  (h_dvd : n ∣ a (n - 1) + 2 ^ (n - 2)) :
  (((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n) = 1 := by
  haveI : Fact n.Prime := ⟨hn_prime⟩
  have h_mul : a (n - 1) * (n - 1).factorial = 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := a_mul_fact n hn2
  have h_mul_zmod : ((a (n - 1) * (n - 1).factorial : ℕ) : ZMod n) = (((2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n)) := by
    rw [h_mul]
  have h_wilson : ((n - 1).factorial : ZMod n) = -1 := ZMod.wilsons_lemma n
  have h_dvd_zmod : (a (n - 1) : ZMod n) + ((2 ^ (n - 2) : ℕ) : ZMod n) = 0 := by
    have h1 : ((a (n - 1) + 2 ^ (n - 2) : ℕ) : ZMod n) = 0 := by
      exact (CharP.cast_eq_zero_iff (ZMod n) n (a (n - 1) + 2 ^ (n - 2))).mpr h_dvd
    have h2 : ((a (n - 1) + 2 ^ (n - 2) : ℕ) : ZMod n) = (a (n - 1) : ZMod n) + ((2 ^ (n - 2) : ℕ) : ZMod n) := Nat.cast_add _ _
    rw [h2] at h1
    exact h1
  have h_a_eq : (a (n - 1) : ZMod n) = - ((2 ^ (n - 2) : ℕ) : ZMod n) := by
    calc (a (n - 1) : ZMod n) = (a (n - 1) : ZMod n) + ((2 ^ (n - 2) : ℕ) : ZMod n) - ((2 ^ (n - 2) : ℕ) : ZMod n) := by ring
      _ = 0 - ((2 ^ (n - 2) : ℕ) : ZMod n) := by rw [h_dvd_zmod]
      _ = - ((2 ^ (n - 2) : ℕ) : ZMod n) := by ring
  have h_RHS_zmod : (((2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n)) = ((2 ^ (n - 2) : ℕ) : ZMod n) * (((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n) := Nat.cast_mul _ _
  have h_LHS_zmod : ((a (n - 1) * (n - 1).factorial : ℕ) : ZMod n) = ((2 ^ (n - 2) : ℕ) : ZMod n) := by
    calc ((a (n - 1) * (n - 1).factorial : ℕ) : ZMod n) = (a (n - 1) : ZMod n) * ((n - 1).factorial : ZMod n) := Nat.cast_mul _ _
      _ = - ((2 ^ (n - 2) : ℕ) : ZMod n) * -1 := by rw [h_wilson, h_a_eq]
      _ = ((2 ^ (n - 2) : ℕ) : ZMod n) := by ring
  rw [h_LHS_zmod, h_RHS_zmod] at h_mul_zmod
  have h_inv : IsUnit ((2 ^ (n - 2) : ℕ) : ZMod n) := by
    have h2 : (2 : ZMod n) ≠ 0 := by
      intro h
      have : n ∣ 2 := (CharP.cast_eq_zero_iff (ZMod n) n 2).mp h
      have : n = 2 := (Nat.prime_dvd_prime_iff_eq hn_prime Nat.prime_two).mp this
      omega
    have h2_unit : IsUnit (2 : ZMod n) := isUnit_iff_ne_zero.mpr h2
    have h2_pow_unit : IsUnit ((2 : ZMod n) ^ (n - 2)) := IsUnit.pow (n - 2) h2_unit
    have h_pow_eq : ((2 ^ (n - 2) : ℕ) : ZMod n) = (2 : ZMod n) ^ (n - 2) := by push_cast; rfl
    rw [h_pow_eq]
    exact h2_pow_unit
  have h_cancel : ((2 ^ (n - 2) : ℕ) : ZMod n) * 1 = ((2 ^ (n - 2) : ℕ) : ZMod n) * (((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n) := by
    calc ((2 ^ (n - 2) : ℕ) : ZMod n) * 1 = ((2 ^ (n - 2) : ℕ) : ZMod n) := by ring
      _ = ((2 ^ (n - 2) : ℕ) : ZMod n) * (((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n) := h_mul_zmod
  have h_cancel2 : 1 = (((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n) := h_inv.mul_left_cancel h_cancel
  exact h_cancel2.symm
