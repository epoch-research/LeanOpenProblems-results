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

lemma bits_1 : (1 : ℕ).bits = [true] := Nat.one_bits

lemma bits_2 : (2 : ℕ).bits = [false, true] := by
  have h_2 : (2 : ℕ) = 2 * 1 := by norm_num
  erw [h_2, Nat.bit0_bits 1 (by decide)]
  rw [Nat.one_bits]

lemma bits_7 : (7 : ℕ).bits = [true, true, true] := by
  have h_7 : (7 : ℕ) = 2 * 3 + 1 := by norm_num
  rw [h_7, Nat.bit1_bits]
  have h_3 : (3 : ℕ) = 2 * 1 + 1 := by norm_num
  rw [h_3, Nat.bit1_bits]
  rw [Nat.one_bits]

lemma bits_8 : (8 : ℕ).bits = [false, false, false, true] := by
  have h_8 : (8 : ℕ) = 2 * 4 := by norm_num
  erw [h_8, Nat.bit0_bits 4 (by decide)]
  have h_4 : (4 : ℕ) = 2 * 2 := by norm_num
  erw [h_4, Nat.bit0_bits 2 (by decide)]
  have h_2 : (2 : ℕ) = 2 * 1 := by norm_num
  erw [h_2, Nat.bit0_bits 1 (by decide)]
  rw [Nat.one_bits]

lemma bits_21 : (21 : ℕ).bits = [true, false, true, false, true] := by
  have h_21 : (21 : ℕ) = 2 * 10 + 1 := by norm_num
  rw [h_21, Nat.bit1_bits]
  have h_10 : (10 : ℕ) = 2 * 5 := by norm_num
  erw [h_10, Nat.bit0_bits 5 (by decide)]
  have h_5 : (5 : ℕ) = 2 * 2 + 1 := by norm_num
  rw [h_5, Nat.bit1_bits]
  have h_2 : (2 : ℕ) = 2 * 1 := by norm_num
  erw [h_2, Nat.bit0_bits 1 (by decide)]
  rw [Nat.one_bits]

lemma bits_28 : (28 : ℕ).bits = [false, false, true, true, true] := by
  have h_28 : (28 : ℕ) = 2 * 14 := by norm_num
  erw [h_28, Nat.bit0_bits 14 (by decide)]
  have h_14 : (14 : ℕ) = 2 * 7 := by norm_num
  erw [h_14, Nat.bit0_bits 7 (by decide)]
  rw [bits_7]

lemma bits_35 : (35 : ℕ).bits = [true, true, false, false, false, true] := by
  have h_35 : (35 : ℕ) = 2 * 17 + 1 := by norm_num
  rw [h_35, Nat.bit1_bits]
  have h_17 : (17 : ℕ) = 2 * 8 + 1 := by norm_num
  rw [h_17, Nat.bit1_bits]
  rw [bits_8]

lemma bits_56 : (56 : ℕ).bits = [false, false, false, true, true, true] := by
  have h_56 : (56 : ℕ) = 2 * 28 := by norm_num
  erw [h_56, Nat.bit0_bits 28 (by decide)]
  rw [bits_28]

lemma bits_70 : (70 : ℕ).bits = [false, true, true, false, false, false, true] := by
  have h_70 : (70 : ℕ) = 2 * 35 := by norm_num
  erw [h_70, Nat.bit0_bits 35 (by decide)]
  rw [bits_35]

theorem a0 : a 0 = 0 := by
  rw [a_eq, a.find_min_m.eq_1]
  simp

theorem a1 : a 1 = 0 := by
  rw [a_eq]
  have hc1 : Nat.choose 1 1 = 1 := rfl
  rw [a.find_min_m.eq_1]; rw [hc1]; simp [bits_1]
  rw [a.find_min_m.eq_1]; simp

theorem a2 : a 2 = 0 := by
  rw [a_eq]
  have hc1 : Nat.choose 2 1 = 2 := rfl
  have hc2 : Nat.choose 2 2 = 1 := rfl
  rw [a.find_min_m.eq_1]; rw [hc1]; simp [bits_2]
  rw [a.find_min_m.eq_1]; rw [hc2]; simp [bits_1]
  rw [a.find_min_m.eq_1]; simp

lemma a7_find : a.find_min_m 7 (fun k => decide ((k.bits.count true % 2) = 0)) 8 = 0 := by
  rw [a.find_min_m.eq_1]
  simp

theorem a7 : a 7 = 0 := by
  rw [a_eq]
  have hc1 : Nat.choose 7 1 = 7 := rfl
  have hc2 : Nat.choose 7 2 = 21 := rfl
  have hc3 : Nat.choose 7 3 = 35 := rfl
  have hc4 : Nat.choose 7 4 = 35 := rfl
  have hc5 : Nat.choose 7 5 = 21 := rfl
  have hc6 : Nat.choose 7 6 = 7 := rfl
  have hc7 : Nat.choose 7 7 = 1 := rfl
  rw [a.find_min_m.eq_1]; rw [hc1]; simp [bits_7]
  rw [a.find_min_m.eq_1]; rw [hc2]; simp [bits_21]
  rw [a.find_min_m.eq_1]; rw [hc3]; simp [bits_35]
  rw [a.find_min_m.eq_1]; rw [hc4]; simp [bits_35]
  rw [a.find_min_m.eq_1]; rw [hc5]; simp [bits_21]
  rw [a.find_min_m.eq_1]; rw [hc6]; simp [bits_7]
  rw [a.find_min_m.eq_1]; rw [hc7]; simp [bits_1]
  exact a7_find

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
  rw [a.find_min_m.eq_1]; rw [hc1]; simp [bits_8]
  rw [a.find_min_m.eq_1]; rw [hc2]; simp [bits_28]
  rw [a.find_min_m.eq_1]; rw [hc3]; simp [bits_56]
  rw [a.find_min_m.eq_1]; rw [hc4]; simp [bits_70]
  rw [a.find_min_m.eq_1]; rw [hc5]; simp [bits_56]
  rw [a.find_min_m.eq_1]; rw [hc6]; simp [bits_28]
  rw [a.find_min_m.eq_1]; rw [hc7]; simp [bits_8]
  rw [a.find_min_m.eq_1]; rw [hc8]; simp [bits_1]
  exact a8_find
