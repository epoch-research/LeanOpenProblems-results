import FormalConjectures.Util.ProblemImports

open Nat List

lemma bits_9 : (9 : ℕ).bits = [true, false, false, true] := by
  have h_9 : (9 : ℕ) = 2 * 4 + 1 := by norm_num
  rw [h_9, Nat.bit1_bits]
  have h_4 : (4 : ℕ) = 2 * 2 := by norm_num
  erw [h_4, Nat.bit0_bits 2 (by decide)]
  have h_2 : (2 : ℕ) = 2 * 1 := by norm_num
  erw [h_2, Nat.bit0_bits 1 (by decide)]
  rw [Nat.one_bits]

lemma bits_10 : (10 : ℕ).bits = [false, true, false, true] := by
  have h_10 : (10 : ℕ) = 2 * 5 := by norm_num
  erw [h_10, Nat.bit0_bits 5 (by decide)]
  have h_5 : (5 : ℕ) = 2 * 2 + 1 := by norm_num
  rw [h_5, Nat.bit1_bits]
  have h_2 : (2 : ℕ) = 2 * 1 := by norm_num
  erw [h_2, Nat.bit0_bits 1 (by decide)]
  rw [Nat.one_bits]

lemma bits_12 : (12 : ℕ).bits = [false, false, true, true] := by
  have h_12 : (12 : ℕ) = 2 * 6 := by norm_num
  erw [h_12, Nat.bit0_bits 6 (by decide)]
  have h_6 : (6 : ℕ) = 2 * 3 := by norm_num
  erw [h_6, Nat.bit0_bits 3 (by decide)]
  have h_3 : (3 : ℕ) = 2 * 1 + 1 := by norm_num
  rw [h_3, Nat.bit1_bits]
  rw [Nat.one_bits]

lemma bits_15 : (15 : ℕ).bits = [true, true, true, true] := by
  have h_15 : (15 : ℕ) = 2 * 7 + 1 := by norm_num
  rw [h_15, Nat.bit1_bits]
  have h_7 : (7 : ℕ) = 2 * 3 + 1 := by norm_num
  rw [h_7, Nat.bit1_bits]
  have h_3 : (3 : ℕ) = 2 * 1 + 1 := by norm_num
  rw [h_3, Nat.bit1_bits]
  rw [Nat.one_bits]

lemma bits_17 : (17 : ℕ).bits = [true, false, false, false, true] := by
  have h_17 : (17 : ℕ) = 2 * 8 + 1 := by norm_num
  rw [h_17, Nat.bit1_bits]
  have h_8 : (8 : ℕ) = 2 * 4 := by norm_num
  erw [h_8, Nat.bit0_bits 4 (by decide)]
  have h_4 : (4 : ℕ) = 2 * 2 := by norm_num
  erw [h_4, Nat.bit0_bits 2 (by decide)]
  have h_2 : (2 : ℕ) = 2 * 1 := by norm_num
  erw [h_2, Nat.bit0_bits 1 (by decide)]
  rw [Nat.one_bits]

lemma bits_165 : (165 : ℕ).bits = [true, false, true, false, false, true, false, true] := by
  have h_165 : (165 : ℕ) = 2 * 82 + 1 := by norm_num
  rw [h_165, Nat.bit1_bits]
  have h_82 : (82 : ℕ) = 2 * 41 := by norm_num
  erw [h_82, Nat.bit0_bits 41 (by decide)]
  have h_41 : (41 : ℕ) = 2 * 20 + 1 := by norm_num
  rw [h_41, Nat.bit1_bits]
  have h_20 : (20 : ℕ) = 2 * 10 := by norm_num
  erw [h_20, Nat.bit0_bits 10 (by decide)]
  have h_10 : (10 : ℕ) = 2 * 5 := by norm_num
  erw [h_10, Nat.bit0_bits 5 (by decide)]
  have h_5 : (5 : ℕ) = 2 * 2 + 1 := by norm_num
  rw [h_5, Nat.bit1_bits]
  have h_2 : (2 : ℕ) = 2 * 1 := by norm_num
  erw [h_2, Nat.bit0_bits 1 (by decide)]
  rw [Nat.one_bits]

lemma bits_78 : (78 : ℕ).bits = [false, true, true, true, false, false, true] := by
  have h_78 : (78 : ℕ) = 2 * 39 := by norm_num
  erw [h_78, Nat.bit0_bits 39 (by decide)]
  have h_39 : (39 : ℕ) = 2 * 19 + 1 := by norm_num
  rw [h_39, Nat.bit1_bits]
  have h_19 : (19 : ℕ) = 2 * 9 + 1 := by norm_num
  rw [h_19, Nat.bit1_bits]
  have h_9 : (9 : ℕ) = 2 * 4 + 1 := by norm_num
  rw [h_9, Nat.bit1_bits]
  have h_4 : (4 : ℕ) = 2 * 2 := by norm_num
  erw [h_4, Nat.bit0_bits 2 (by decide)]
  have h_2 : (2 : ℕ) = 2 * 1 := by norm_num
  erw [h_2, Nat.bit0_bits 1 (by decide)]
  rw [Nat.one_bits]

lemma bits_3432 : (3432 : ℕ).bits = [false, false, false, true, false, true, true, false, true, false, true, true] := by
  have h_3432 : (3432 : ℕ) = 2 * 1716 := by norm_num
  erw [h_3432, Nat.bit0_bits 1716 (by decide)]
  have h_1716 : (1716 : ℕ) = 2 * 858 := by norm_num
  erw [h_1716, Nat.bit0_bits 858 (by decide)]
  have h_858 : (858 : ℕ) = 2 * 429 := by norm_num
  erw [h_858, Nat.bit0_bits 429 (by decide)]
  have h_429 : (429 : ℕ) = 2 * 214 + 1 := by norm_num
  rw [h_429, Nat.bit1_bits]
  have h_214 : (214 : ℕ) = 2 * 107 := by norm_num
  erw [h_214, Nat.bit0_bits 107 (by decide)]
  have h_107 : (107 : ℕ) = 2 * 53 + 1 := by norm_num
  rw [h_107, Nat.bit1_bits]
  have h_53 : (53 : ℕ) = 2 * 26 + 1 := by norm_num
  rw [h_53, Nat.bit1_bits]
  have h_26 : (26 : ℕ) = 2 * 13 := by norm_num
  erw [h_26, Nat.bit0_bits 13 (by decide)]
  have h_13 : (13 : ℕ) = 2 * 6 + 1 := by norm_num
  rw [h_13, Nat.bit1_bits]
  have h_6 : (6 : ℕ) = 2 * 3 := by norm_num
  erw [h_6, Nat.bit0_bits 3 (by decide)]
  have h_3 : (3 : ℕ) = 2 * 1 + 1 := by norm_num
  rw [h_3, Nat.bit1_bits]
  rw [Nat.one_bits]

lemma bits_120 : (120 : ℕ).bits = [false, false, false, true, true, true, true] := by
  have h_120 : (120 : ℕ) = 2 * 60 := by norm_num
  erw [h_120, Nat.bit0_bits 60 (by decide)]
  have h_60 : (60 : ℕ) = 2 * 30 := by norm_num
  erw [h_60, Nat.bit0_bits 30 (by decide)]
  have h_30 : (30 : ℕ) = 2 * 15 := by norm_num
  erw [h_30, Nat.bit0_bits 15 (by decide)]
  have h_15 : (15 : ℕ) = 2 * 7 + 1 := by norm_num
  rw [h_15, Nat.bit1_bits]
  have h_7 : (7 : ℕ) = 2 * 3 + 1 := by norm_num
  rw [h_7, Nat.bit1_bits]
  have h_3 : (3 : ℕ) = 2 * 1 + 1 := by norm_num
  rw [h_3, Nat.bit1_bits]
  rw [Nat.one_bits]
