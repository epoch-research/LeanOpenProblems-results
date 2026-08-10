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

lemma find_min_m_ge_of_exists {n m k : ℕ} (hmk : m ≤ k) (hkn : k ≤ n)
    (hevil : ((n.choose k).bits.count true % 2) = 0) :
    a.find_min_m n (fun k => decide ((k.bits.count true % 2) = 0)) m ≥ m := by
  let is_evil_fn := fun (k : ℕ) => decide ((k.bits.count true % 2) = 0)
  have hevil_bool : is_evil_fn (n.choose k) = true := by
    dsimp [is_evil_fn]
    rw [decide_eq_true_iff]
    exact hevil
  induction m using a.find_min_m.induct n is_evil_fn with
  | case1 x hx =>
    omega
  | case2 x hx he =>
    have h_cond : List.count true (n.choose x).bits % 2 = 0 := by
      exact decide_eq_true_iff.mp he
    rw [a.find_min_m.eq_1]
    have hx_not : ¬x > n := hx
    simp [hx_not, h_cond]
  | case3 x hx hne ih =>
    have h_cond : ¬(List.count true (n.choose x).bits % 2 = 0) := by
      rw [decide_eq_true_iff] at hne
      exact hne
    rw [a.find_min_m.eq_1]
    have hx_not : ¬x > n := hx
    simp [hx_not, h_cond]
    have h_xk : x < k := by
      by_contra hc
      have : x = k := by omega
      subst this
      exact h_cond hevil
    have h_x1k : x + 1 ≤ k := by omega
    have ih_val := ih h_x1k
    omega

lemma a_eq (n : ℕ) : a n = a.find_min_m n (fun k => decide ((k.bits.count true % 2) = 0)) 1 := rfl

lemma a_ne_zero_of_exists {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hevil : ((n.choose k).bits.count true % 2) = 0) :
    a n ≠ 0 := by
  rw [a_eq]
  have : a.find_min_m n (fun k => decide ((k.bits.count true % 2) = 0)) 1 ≥ 1 :=
    find_min_m_ge_of_exists hk1 hkn hevil
  omega

lemma a_ne_zero_of_even_popcount {n : ℕ} (hn1 : 1 ≤ n) (heven : n.bits.count true % 2 = 0) : a n ≠ 0 := by
  apply a_ne_zero_of_exists (k := 1) (by omega) hn1
  rw [Nat.choose_one_right]
  exact heven

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

lemma a9_ne_zero : a 9 ≠ 0 := by
  apply a_ne_zero_of_even_popcount (by omega)
  rw [bits_9]
  rfl

lemma a10_ne_zero : a 10 ≠ 0 := by
  apply a_ne_zero_of_even_popcount (by omega)
  rw [bits_10]
  rfl

lemma a11_ne_zero : a 11 ≠ 0 := by
  apply a_ne_zero_of_exists (k := 3) (by omega) (by omega)
  have h_choose : Nat.choose 11 3 = 165 := rfl
  rw [h_choose, bits_165]
  rfl

lemma a12_ne_zero : a 12 ≠ 0 := by
  apply a_ne_zero_of_even_popcount (by omega)
  rw [bits_12]
  rfl

lemma a13_ne_zero : a 13 ≠ 0 := by
  apply a_ne_zero_of_exists (k := 2) (by omega) (by omega)
  have h_choose : Nat.choose 13 2 = 78 := rfl
  rw [h_choose, bits_78]
  rfl

lemma a14_ne_zero : a 14 ≠ 0 := by
  apply a_ne_zero_of_exists (k := 7) (by omega) (by omega)
  have h_choose : Nat.choose 14 7 = 3432 := rfl
  rw [h_choose, bits_3432]
  rfl

lemma a15_ne_zero : a 15 ≠ 0 := by
  apply a_ne_zero_of_even_popcount (by omega)
  rw [bits_15]
  rfl

lemma a16_ne_zero : a 16 ≠ 0 := by
  apply a_ne_zero_of_exists (k := 2) (by omega) (by omega)
  have h_choose : Nat.choose 16 2 = 120 := rfl
  rw [h_choose, bits_120]
  rfl

lemma a17_ne_zero : a 17 ≠ 0 := by
  apply a_ne_zero_of_even_popcount (by omega)
  rw [bits_17]
  rfl
