import FormalConjectures.Util.ProblemImports

open Nat List

def a (n : ℕ) : ℕ :=
  let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0
  let rec find_min_m (m : ℕ) : ℕ :=
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m (m + 1)
    termination_by n + 1 - m
  find_min_m 1

lemma a_eq (n : ℕ) : a n = a.find_min_m n (fun k => decide ((k.bits.count true % 2) = 0)) 1 := rfl

lemma bits_7 : (7 : ℕ).bits = [true, true, true] := by
  have h_7 : (7 : ℕ) = 2 * 3 + 1 := by norm_num
  rw [h_7, Nat.bit1_bits]
  have h_3 : (3 : ℕ) = 2 * 1 + 1 := by norm_num
  rw [h_3, Nat.bit1_bits]
  rw [Nat.one_bits]

lemma bits_35 : (35 : ℕ).bits = [true, true, false, false, false, true] := by
  have h_35 : (35 : ℕ) = 2 * 17 + 1 := by norm_num
  rw [h_35, Nat.bit1_bits]
  have h_17 : (17 : ℕ) = 2 * 8 + 1 := by norm_num
  rw [h_17, Nat.bit1_bits]
  have h_8 : (8 : ℕ) = 2 * 4 := by norm_num
  erw [h_8, Nat.bit0_bits 4 (by decide)]
  have h_4 : (4 : ℕ) = 2 * 2 := by norm_num
  erw [h_4, Nat.bit0_bits 2 (by decide)]
  have h_2 : (2 : ℕ) = 2 * 1 := by norm_num
  erw [h_2, Nat.bit0_bits 1 (by decide)]
  rw [Nat.one_bits]

lemma bits_8 : (8 : ℕ).bits = [false, false, false, true] := by
  have h_8 : (8 : ℕ) = 2 * 4 := by norm_num
  erw [h_8, Nat.bit0_bits 4 (by decide)]
  have h_4 : (4 : ℕ) = 2 * 2 := by norm_num
  erw [h_4, Nat.bit0_bits 2 (by decide)]
  have h_2 : (2 : ℕ) = 2 * 1 := by norm_num
  erw [h_2, Nat.bit0_bits 1 (by decide)]
  rw [Nat.one_bits]

lemma bits_28 : (28 : ℕ).bits = [false, false, true, true, true] := by
  have h_28 : (28 : ℕ) = 2 * 14 := by norm_num
  erw [h_28, Nat.bit0_bits 14 (by decide)]
  have h_14 : (14 : ℕ) = 2 * 7 := by norm_num
  erw [h_14, Nat.bit0_bits 7 (by decide)]
  have h_7 : (7 : ℕ) = 2 * 3 + 1 := by norm_num
  rw [h_7, Nat.bit1_bits]
  have h_3 : (3 : ℕ) = 2 * 1 + 1 := by norm_num
  rw [h_3, Nat.bit1_bits]
  rw [Nat.one_bits]

lemma bits_56 : (56 : ℕ).bits = [false, false, false, true, true, true] := by
  have h_56 : (56 : ℕ) = 2 * 28 := by norm_num
  erw [h_56, Nat.bit0_bits 28 (by decide)]
  rw [bits_28]

lemma bits_70 : (70 : ℕ).bits = [false, true, true, false, false, false, true] := by
  have h_70 : (70 : ℕ) = 2 * 35 := by norm_num
  erw [h_70, Nat.bit0_bits 35 (by decide)]
  rw [bits_35]

lemma a8_find : a.find_min_m 8 (fun k => decide ((k.bits.count true % 2) = 0)) 9 = 0 := by
  rw [a.find_min_m.eq_1]
  simp

theorem a8 : a 8 = 0 := by
  rw [a_eq]
  have hc1 : Nat.choose 8 1 = 8 := rfl
  have hc2 : Nat.choose 8 2 = 28 := rfl
  have hc3 : Nat.choose 8 3 = 56 := rfl
  have hc4 : Nat.choose 8 4 = 70 := rfl
  have hc5 : Nat.choose 8 5 = 56 := rfl
  have hc6 : Nat.choose 8 6 = 28 := rfl
  have hc7 : Nat.choose 8 7 = 8 := rfl
  have hc8 : Nat.choose 8 8 = 1 := rfl
  rw [a.find_min_m.eq_1]; rw [hc1]; simp; rw [bits_8]; simp
  rw [a.find_min_m.eq_1]; rw [hc2]; simp; rw [bits_28]; simp
  rw [a.find_min_m.eq_1]; rw [hc3]; simp; rw [bits_56]; simp
  rw [a.find_min_m.eq_1]; rw [hc4]; simp; rw [bits_70]; simp
  rw [a.find_min_m.eq_1]; rw [hc5]; simp; rw [bits_56]; simp
  rw [a.find_min_m.eq_1]; rw [hc6]; simp; rw [bits_28]; simp
  rw [a.find_min_m.eq_1]; rw [hc7]; simp; rw [bits_8]; simp
  rw [a.find_min_m.eq_1]; rw [hc8]; simp
  exact a8_find
