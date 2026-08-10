import Mathlib

open Nat

theorem mem_digits_iff_getD {b n d : ℕ} (_hb : 2 ≤ b) (h : d ∈ Nat.digits b n) :
    ∃ i, d = (Nat.digits b n).getD i 0 := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem.mp h
  obtain ⟨h_lt, h_eq⟩ := hi
  use i
  rw [List.getD_eq_getElem (Nat.digits b n) 0 h_lt]
  exact h_eq.symm

theorem digits_11101 : ∀ d ∈ Nat.digits 10 11101, d = 0 ∨ d = 1 := by
  intro d hd
  obtain ⟨i, hi⟩ := mem_digits_iff_getD (by decide) hd
  rw [hi, Nat.getD_digits 11101 i (by decide)]
  rcases lt_or_ge i 5 with hi5 | hi5
  · interval_cases i <;> decide
  · have h_pow : 10 ^ i ≥ 100000 := by
      calc 10 ^ i ≥ 10 ^ 5 := Nat.pow_le_pow_right (by decide) hi5
      _ = 100000 := by decide
    have h_div : 11101 / 10 ^ i = 0 := by
      apply Nat.div_eq_of_lt
      omega
    rw [h_div]
    decide

#check @Nat.pow_pos



theorem ten_pow_lt_two_pow_factor (k : ℕ) (hk : k ≥ 2) : 1310 * 10 ^ k < 2 ^ (9 * k - 1) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases k with _ | k
    · omega
    · -- now k + 2
      rcases k with _ | k
      · -- k = 0, so k + 2 = 2
        decide
      · -- k >= 1, so k + 2 >= 3. we can use ih for k + 1
        have h_step : 1310 * 10 ^ (k + 3) = 10 * (1310 * 10 ^ (k + 2)) := by
          calc 1310 * 10 ^ (k + 3) = 1310 * (10 ^ (k + 2) * 10) := by rfl
          _ = 10 * (1310 * 10 ^ (k + 2)) := by ring
        rw [h_step]
        have ih_inst := ih (by omega)
        have h_mul : 10 * (1310 * 10 ^ (k + 2)) < 10 * 2 ^ (9 * (k + 2) - 1) := by
          exact Nat.mul_lt_mul_of_pos_left ih_inst (by decide)
        have h_le : 10 * 2 ^ (9 * (k + 2) - 1) < 2 ^ (9 * (k + 3) - 1) := by
          have h_pow_eq : 9 * (k + 3) - 1 = (9 * (k + 2) - 1) + 9 := by omega
          rw [h_pow_eq, pow_add]
          have h_pow9 : 2 ^ 9 = 512 := by decide
          rw [h_pow9]
          have : 10 < 512 := by decide
          exact Nat.mul_lt_mul_of_pos_right this (Nat.pow_pos (by decide))
        exact lt_trans h_mul h_le


theorem d_lt_two_pow_factor (k c d L : ℕ) (hk2 : k ≥ 2) (h_lt : d * 2 ^ c < 10 ^ k) (h_L : 9 * k - 1 = L + c) :
    1310 * d < 2 ^ L := by
  have h1 : 1310 * (d * 2 ^ c) < 1310 * 10 ^ k := Nat.mul_lt_mul_of_pos_left h_lt (by decide)
  have h2 := ten_pow_lt_two_pow_factor k hk2
  have h3 : 1310 * (d * 2 ^ c) < 2 ^ (9 * k - 1) := lt_trans h1 h2
  have h4 : 1310 * (d * 2 ^ c) = (1310 * d) * 2 ^ c := by ring
  rw [h4] at h3
  rw [h_L] at h3
  rw [pow_add] at h3
  have h5 : 2 ^ c > 0 := Nat.pow_pos (by decide)
  exact Nat.lt_of_mul_lt_mul_right h3


theorem d_le_L_of_L_lt_15 (d L : ℕ) (hd_pos : d > 0) (h_L15 : L < 15) (h_lt : 1310 * d < 2 ^ L) :
    d ≤ L := by
  interval_cases L <;> omega




theorem digits_member (M : ℕ) (h_pos : 0 < M) (d : ℕ) (h_dvd : d ∣ M) (h_digits : ∀ x ∈ Nat.digits 10 M, x = 0 ∨ x = 1) :
    A004290 d ≤ M := by
  have hS : M ∈ { m : ℕ | 0 < m ∧ d ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := ⟨h_pos, h_dvd, h_digits⟩
  exact Nat.sInf_le hS

theorem digits_11001 : ∀ d ∈ Nat.digits 10 11001, d = 0 ∨ d = 1 := by
  intro d hd
  obtain ⟨i, hi⟩ := mem_digits_iff_getD (by decide) hd
  rw [hi, Nat.getD_digits 11001 i (by decide)]
  rcases lt_or_ge i 5 with hi5 | hi5
  · interval_cases i <;> decide
  · have h_pow : 10 ^ i ≥ 100000 := by
      calc 10 ^ i ≥ 10 ^ 5 := Nat.pow_le_pow_right (by decide) hi5
      _ = 100000 := by decide
    have h_div : 11001 / 10 ^ i = 0 := by
      apply Nat.div_eq_of_lt
      omega
    rw [h_div]
    decide

theorem digits_10101 : ∀ d ∈ Nat.digits 10 10101, d = 0 ∨ d = 1 := by
  intro d hd
  obtain ⟨i, hi⟩ := mem_digits_iff_getD (by decide) hd
  rw [hi, Nat.getD_digits 10101 i (by decide)]
  rcases lt_or_ge i 5 with hi5 | hi5
  · interval_cases i <;> decide
  · have h_pow : 10 ^ i ≥ 100000 := by
      calc 10 ^ i ≥ 10 ^ 5 := Nat.pow_le_pow_right (by decide) hi5
      _ = 100000 := by decide
    have h_div : 10101 / 10 ^ i = 0 := by
      apply Nat.div_eq_of_lt
      omega
    rw [h_div]
    decide

theorem digits_110101 : ∀ d ∈ Nat.digits 10 110101, d = 0 ∨ d = 1 := by
  intro d hd
  obtain ⟨i, hi⟩ := mem_digits_iff_getD (by decide) hd
  rw [hi, Nat.getD_digits 110101 i (by decide)]
  rcases lt_or_ge i 6 with hi6 | hi6
  · interval_cases i <;> decide
  · have h_pow : 10 ^ i ≥ 1000000 := by
      calc 10 ^ i ≥ 10 ^ 6 := Nat.pow_le_pow_right (by decide) hi6
      _ = 1000000 := by decide
    have h_div : 110101 / 10 ^ i = 0 := by
      apply Nat.div_eq_of_lt
      omega
    rw [h_div]
    decide

theorem A004290_17 : A004290 17 < 10 ^ 15 := by
  have h : A004290 17 ≤ 11101 := digits_member 11101 (by decide) 17 (by decide) digits_11101
  omega

theorem A004290_19 : A004290 19 < 10 ^ 15 := by
  have h : A004290 19 ≤ 11001 := digits_member 11001 (by decide) 19 (by decide) digits_11001
  omega

theorem A004290_21 : A004290 21 < 10 ^ 15 := by
  have h : A004290 21 ≤ 10101 := digits_member 10101 (by decide) 21 (by decide) digits_10101
  omega

theorem A004290_23 : A004290 23 < 10 ^ 15 := by
  have h : A004290 23 ≤ 110101 := digits_member 110101 (by decide) 23 (by decide) digits_110101
  omega

