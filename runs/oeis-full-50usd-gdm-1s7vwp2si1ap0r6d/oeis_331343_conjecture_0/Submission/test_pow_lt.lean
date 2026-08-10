import FormalConjectures.Util.ProblemImports

open Nat

lemma padicValNat_two_pow_sub_one_lt (p : ℕ) [hp : Fact p.Prime] (hp3 : p ≥ 3) (m : ℕ) (hm : m > 0) :
    padicValNat p (2^m - 1) < m := by
  have h_pos : 2^m - 1 > 0 := by
    have : 2^m ≥ 2^1 := Nat.pow_le_pow_right (by decide) hm
    omega
  have hdvd : p^(padicValNat p (2^m - 1)) ∣ 2^m - 1 := pow_padicValNat_dvd
  have h_le2 : p^(padicValNat p (2^m - 1)) ≤ 2^m - 1 := Nat.le_of_dvd h_pos hdvd
  have h_lt : 2^m - 1 < 2^m := by omega
  have h_lt2 : (2 : ℕ)^m < p^m := by
    have : (2 : ℕ) < p := by omega
    exact Nat.pow_lt_pow_left this hm.ne'
  have h_lt3 : p^(padicValNat p (2^m - 1)) < p^m := by
    calc p^(padicValNat p (2^m - 1)) ≤ 2^m - 1 := h_le2
         _ < 2^m := h_lt
         _ < p^m := h_lt2
  have hp2 : p > 1 := hp.out.two_le
  rwa [Nat.pow_lt_pow_iff_right hp2] at h_lt3

lemma padicValNat_add_eq_of_lt {p : ℕ} [hp : Fact p.Prime] {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hval : padicValNat p A < padicValNat p B) :
    padicValNat p (A + B) = padicValNat p A := by
  have h_rat : padicValRat p (A + B : ℚ) = padicValRat p (A : ℚ) := by
    have h_sum_ne : (A : ℚ) + (B : ℚ) ≠ 0 := by
      have : (A + B : ℚ) = ((A + B : ℕ) : ℚ) := by simp
      rw [this]
      exact Nat.cast_ne_zero.mpr (by omega)
    have h_A_ne : (A : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hA
    have h_B_ne : (B : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hB
    have h_val_lt : padicValRat p (A : ℚ) < padicValRat p (B : ℚ) := by
      rw [← padicValRat_of_nat, ← padicValRat_of_nat]
      exact Int.ofNat_lt.mpr hval
    exact padicValRat.add_eq_of_lt h_sum_ne h_A_ne h_B_ne h_val_lt
  have h_rat' : padicValRat p (↑(A + B) : ℚ) = padicValRat p (A : ℚ) := by
    have h_eq_cast : (↑A + ↑B : ℚ) = (↑(A + B) : ℚ) := by simp
    rw [← h_eq_cast]
    exact h_rat
  rw [← padicValRat_of_nat, ← padicValRat_of_nat] at h_rat'
  exact Nat.cast_inj.mp h_rat'

