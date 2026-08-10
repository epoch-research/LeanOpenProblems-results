import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  let N : ℕ := 2 * n - 1
  let B : ℕ := N.log2 + 1
  let X_range : Finset ℕ := Finset.Icc 1 B
  let Y_range : Finset ℕ := Finset.Icc 1 B
  (Finset.product X_range Y_range).sum fun pair =>
    let x := pair.fst
    let y := pair.snd
    let sum_of_powers := 2 ^ x + 11 * 2 ^ y
    if N > sum_of_powers then
      let p := N - sum_of_powers
      if Nat.Prime p ∧ p % 6 = 1 then 1 else 0
    else
      0

lemma summand_1_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 1) :
  (if 1 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (1 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (1 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl

lemma summand_1_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 1) (hy1 : 1 ≤ y) (hy2 : y ≤ 1) :
  (if 1 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (1 - (2 ^ x + 11 * 2 ^ y)) ∧ (1 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_1_eq_zero_x1 y hy1 hy2

theorem a_eq_zero_1 : a 1 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 1 at hx2
  change y ≤ 1 at hy2
  exact summand_1_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_2_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 2) :
  (if 3 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (3 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (3 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl

lemma summand_2_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 2) :
  (if 3 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (3 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (3 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl

lemma summand_2_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 2) (hy1 : 1 ≤ y) (hy2 : y ≤ 2) :
  (if 3 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (3 - (2 ^ x + 11 * 2 ^ y)) ∧ (3 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_2_eq_zero_x1 y hy1 hy2
  · exact summand_2_eq_zero_x2 y hy1 hy2

theorem a_eq_zero_2 : a 2 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 2 at hx2
  change y ≤ 2 at hy2
  exact summand_2_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_3_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 3) :
  (if 5 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (5 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (5 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl

lemma summand_3_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 3) :
  (if 5 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (5 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (5 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl

lemma summand_3_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 3) :
  (if 5 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (5 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (5 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl

lemma summand_3_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 3) (hy1 : 1 ≤ y) (hy2 : y ≤ 3) :
  (if 5 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (5 - (2 ^ x + 11 * 2 ^ y)) ∧ (5 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_3_eq_zero_x1 y hy1 hy2
  · exact summand_3_eq_zero_x2 y hy1 hy2
  · exact summand_3_eq_zero_x3 y hy1 hy2

theorem a_eq_zero_3 : a 3 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 3 at hx2
  change y ≤ 3 at hy2
  exact summand_3_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_4_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 3) :
  (if 7 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (7 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (7 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl

lemma summand_4_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 3) :
  (if 7 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (7 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (7 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl

lemma summand_4_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 3) :
  (if 7 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (7 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (7 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl

lemma summand_4_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 3) (hy1 : 1 ≤ y) (hy2 : y ≤ 3) :
  (if 7 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (7 - (2 ^ x + 11 * 2 ^ y)) ∧ (7 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_4_eq_zero_x1 y hy1 hy2
  · exact summand_4_eq_zero_x2 y hy1 hy2
  · exact summand_4_eq_zero_x3 y hy1 hy2

theorem a_eq_zero_4 : a 4 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 3 at hx2
  change y ≤ 3 at hy2
  exact summand_4_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_5_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 9 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (9 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (9 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl

lemma summand_5_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 9 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (9 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (9 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl

lemma summand_5_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 9 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (9 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (9 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl

lemma summand_5_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 9 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (9 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (9 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl

lemma summand_5_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 4) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 9 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (9 - (2 ^ x + 11 * 2 ^ y)) ∧ (9 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_5_eq_zero_x1 y hy1 hy2
  · exact summand_5_eq_zero_x2 y hy1 hy2
  · exact summand_5_eq_zero_x3 y hy1 hy2
  · exact summand_5_eq_zero_x4 y hy1 hy2

theorem a_eq_zero_5 : a 5 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 4 at hx2
  change y ≤ 4 at hy2
  exact summand_5_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_6_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 11 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (11 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (11 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl

lemma summand_6_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 11 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (11 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (11 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl

lemma summand_6_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 11 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (11 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (11 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl

lemma summand_6_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 11 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (11 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (11 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl

lemma summand_6_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 4) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 11 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (11 - (2 ^ x + 11 * 2 ^ y)) ∧ (11 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_6_eq_zero_x1 y hy1 hy2
  · exact summand_6_eq_zero_x2 y hy1 hy2
  · exact summand_6_eq_zero_x3 y hy1 hy2
  · exact summand_6_eq_zero_x4 y hy1 hy2

theorem a_eq_zero_6 : a 6 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 4 at hx2
  change y ≤ 4 at hy2
  exact summand_6_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_7_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 13 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (13 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (13 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl

lemma summand_7_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 13 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (13 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (13 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl

lemma summand_7_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 13 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (13 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (13 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl

lemma summand_7_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 13 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (13 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (13 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl

lemma summand_7_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 4) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 13 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (13 - (2 ^ x + 11 * 2 ^ y)) ∧ (13 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_7_eq_zero_x1 y hy1 hy2
  · exact summand_7_eq_zero_x2 y hy1 hy2
  · exact summand_7_eq_zero_x3 y hy1 hy2
  · exact summand_7_eq_zero_x4 y hy1 hy2

theorem a_eq_zero_7 : a 7 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 4 at hx2
  change y ≤ 4 at hy2
  exact summand_7_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_8_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 15 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (15 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (15 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl

lemma summand_8_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 15 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (15 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (15 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl

lemma summand_8_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 15 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (15 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (15 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl

lemma summand_8_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 15 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (15 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (15 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl

lemma summand_8_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 4) (hy1 : 1 ≤ y) (hy2 : y ≤ 4) :
  (if 15 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (15 - (2 ^ x + 11 * 2 ^ y)) ∧ (15 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_8_eq_zero_x1 y hy1 hy2
  · exact summand_8_eq_zero_x2 y hy1 hy2
  · exact summand_8_eq_zero_x3 y hy1 hy2
  · exact summand_8_eq_zero_x4 y hy1 hy2

theorem a_eq_zero_8 : a 8 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 4 at hx2
  change y ≤ 4 at hy2
  exact summand_8_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_9_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 17 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (17 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (17 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_9_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 17 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (17 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (17 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_9_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 17 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (17 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (17 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_9_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 17 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (17 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (17 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_9_eq_zero_x5 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 17 > 2 ^ 5 + 11 * 2 ^ y then
    if Nat.Prime (17 - (2 ^ 5 + 11 * 2 ^ y)) ∧ (17 - (2 ^ 5 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_9_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 5) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 17 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (17 - (2 ^ x + 11 * 2 ^ y)) ∧ (17 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_9_eq_zero_x1 y hy1 hy2
  · exact summand_9_eq_zero_x2 y hy1 hy2
  · exact summand_9_eq_zero_x3 y hy1 hy2
  · exact summand_9_eq_zero_x4 y hy1 hy2
  · exact summand_9_eq_zero_x5 y hy1 hy2

theorem a_eq_zero_9 : a 9 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 5 at hx2
  change y ≤ 5 at hy2
  exact summand_9_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_10_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 19 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (19 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (19 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_10_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 19 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (19 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (19 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_10_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 19 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (19 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (19 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_10_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 19 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (19 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (19 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_10_eq_zero_x5 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 19 > 2 ^ 5 + 11 * 2 ^ y then
    if Nat.Prime (19 - (2 ^ 5 + 11 * 2 ^ y)) ∧ (19 - (2 ^ 5 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_10_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 5) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 19 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (19 - (2 ^ x + 11 * 2 ^ y)) ∧ (19 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_10_eq_zero_x1 y hy1 hy2
  · exact summand_10_eq_zero_x2 y hy1 hy2
  · exact summand_10_eq_zero_x3 y hy1 hy2
  · exact summand_10_eq_zero_x4 y hy1 hy2
  · exact summand_10_eq_zero_x5 y hy1 hy2

theorem a_eq_zero_10 : a 10 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 5 at hx2
  change y ≤ 5 at hy2
  exact summand_10_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_11_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 21 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (21 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (21 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_11_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 21 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (21 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (21 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_11_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 21 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (21 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (21 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_11_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 21 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (21 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (21 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_11_eq_zero_x5 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 21 > 2 ^ 5 + 11 * 2 ^ y then
    if Nat.Prime (21 - (2 ^ 5 + 11 * 2 ^ y)) ∧ (21 - (2 ^ 5 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_11_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 5) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 21 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (21 - (2 ^ x + 11 * 2 ^ y)) ∧ (21 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_11_eq_zero_x1 y hy1 hy2
  · exact summand_11_eq_zero_x2 y hy1 hy2
  · exact summand_11_eq_zero_x3 y hy1 hy2
  · exact summand_11_eq_zero_x4 y hy1 hy2
  · exact summand_11_eq_zero_x5 y hy1 hy2

theorem a_eq_zero_11 : a 11 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 5 at hx2
  change y ≤ 5 at hy2
  exact summand_11_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_12_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 23 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (23 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (23 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_12_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 23 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (23 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (23 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_12_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 23 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (23 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (23 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_12_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 23 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (23 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (23 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_12_eq_zero_x5 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 23 > 2 ^ 5 + 11 * 2 ^ y then
    if Nat.Prime (23 - (2 ^ 5 + 11 * 2 ^ y)) ∧ (23 - (2 ^ 5 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_12_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 5) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 23 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (23 - (2 ^ x + 11 * 2 ^ y)) ∧ (23 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_12_eq_zero_x1 y hy1 hy2
  · exact summand_12_eq_zero_x2 y hy1 hy2
  · exact summand_12_eq_zero_x3 y hy1 hy2
  · exact summand_12_eq_zero_x4 y hy1 hy2
  · exact summand_12_eq_zero_x5 y hy1 hy2

theorem a_eq_zero_12 : a 12 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 5 at hx2
  change y ≤ 5 at hy2
  exact summand_12_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_13_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 25 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (25 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (25 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 25 > 2 ^ 1 + 11 * 2 ^ 1 := by decide
    have h_eq : 25 - (2 ^ 1 + 11 * 2 ^ 1) = 1 := by rfl
    have h_not_prime : ¬ Nat.Prime 1 := Nat.not_prime_one
    have h_and : ¬ (Nat.Prime 1 ∧ 1 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_13_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 25 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (25 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (25 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_13_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 25 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (25 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (25 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_13_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 25 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (25 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (25 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_13_eq_zero_x5 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 25 > 2 ^ 5 + 11 * 2 ^ y then
    if Nat.Prime (25 - (2 ^ 5 + 11 * 2 ^ y)) ∧ (25 - (2 ^ 5 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_13_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 5) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 25 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (25 - (2 ^ x + 11 * 2 ^ y)) ∧ (25 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_13_eq_zero_x1 y hy1 hy2
  · exact summand_13_eq_zero_x2 y hy1 hy2
  · exact summand_13_eq_zero_x3 y hy1 hy2
  · exact summand_13_eq_zero_x4 y hy1 hy2
  · exact summand_13_eq_zero_x5 y hy1 hy2

theorem a_eq_zero_13 : a 13 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 5 at hx2
  change y ≤ 5 at hy2
  exact summand_13_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_14_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 27 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (27 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (27 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 27 > 2 ^ 1 + 11 * 2 ^ 1 := by decide
    have h_eq : 27 - (2 ^ 1 + 11 * 2 ^ 1) = 3 := by rfl
    have h_mod : 3 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 3 ∧ 3 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_14_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 27 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (27 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (27 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 27 > 2 ^ 2 + 11 * 2 ^ 1 := by decide
    have h_eq : 27 - (2 ^ 2 + 11 * 2 ^ 1) = 1 := by rfl
    have h_not_prime : ¬ Nat.Prime 1 := Nat.not_prime_one
    have h_and : ¬ (Nat.Prime 1 ∧ 1 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_14_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 27 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (27 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (27 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_14_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 27 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (27 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (27 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_14_eq_zero_x5 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 27 > 2 ^ 5 + 11 * 2 ^ y then
    if Nat.Prime (27 - (2 ^ 5 + 11 * 2 ^ y)) ∧ (27 - (2 ^ 5 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_14_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 5) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 27 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (27 - (2 ^ x + 11 * 2 ^ y)) ∧ (27 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_14_eq_zero_x1 y hy1 hy2
  · exact summand_14_eq_zero_x2 y hy1 hy2
  · exact summand_14_eq_zero_x3 y hy1 hy2
  · exact summand_14_eq_zero_x4 y hy1 hy2
  · exact summand_14_eq_zero_x5 y hy1 hy2

theorem a_eq_zero_14 : a 14 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 5 at hx2
  change y ≤ 5 at hy2
  exact summand_14_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_15_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 29 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (29 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (29 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 29 > 2 ^ 1 + 11 * 2 ^ 1 := by decide
    have h_eq : 29 - (2 ^ 1 + 11 * 2 ^ 1) = 5 := by rfl
    have h_mod : 5 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 5 ∧ 5 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_15_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 29 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (29 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (29 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 29 > 2 ^ 2 + 11 * 2 ^ 1 := by decide
    have h_eq : 29 - (2 ^ 2 + 11 * 2 ^ 1) = 3 := by rfl
    have h_mod : 3 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 3 ∧ 3 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_15_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 29 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (29 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (29 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_15_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 29 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (29 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (29 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_15_eq_zero_x5 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 29 > 2 ^ 5 + 11 * 2 ^ y then
    if Nat.Prime (29 - (2 ^ 5 + 11 * 2 ^ y)) ∧ (29 - (2 ^ 5 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl

lemma summand_15_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 5) (hy1 : 1 ≤ y) (hy2 : y ≤ 5) :
  (if 29 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (29 - (2 ^ x + 11 * 2 ^ y)) ∧ (29 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_15_eq_zero_x1 y hy1 hy2
  · exact summand_15_eq_zero_x2 y hy1 hy2
  · exact summand_15_eq_zero_x3 y hy1 hy2
  · exact summand_15_eq_zero_x4 y hy1 hy2
  · exact summand_15_eq_zero_x5 y hy1 hy2

theorem a_eq_zero_15 : a 15 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 5 at hx2
  change y ≤ 5 at hy2
  exact summand_15_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_18_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 35 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (35 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (35 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 35 > 2 ^ 1 + 11 * 2 ^ 1 := by decide
    have h_eq : 35 - (2 ^ 1 + 11 * 2 ^ 1) = 11 := by rfl
    have h_mod : 11 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 11 ∧ 11 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_18_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 35 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (35 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (35 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 35 > 2 ^ 2 + 11 * 2 ^ 1 := by decide
    have h_eq : 35 - (2 ^ 2 + 11 * 2 ^ 1) = 9 := by rfl
    have h_mod : 9 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 9 ∧ 9 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_18_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 35 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (35 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (35 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 35 > 2 ^ 3 + 11 * 2 ^ 1 := by decide
    have h_eq : 35 - (2 ^ 3 + 11 * 2 ^ 1) = 5 := by rfl
    have h_mod : 5 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 5 ∧ 5 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_18_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 35 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (35 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (35 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_18_eq_zero_x5 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 35 > 2 ^ 5 + 11 * 2 ^ y then
    if Nat.Prime (35 - (2 ^ 5 + 11 * 2 ^ y)) ∧ (35 - (2 ^ 5 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_18_eq_zero_x6 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 35 > 2 ^ 6 + 11 * 2 ^ y then
    if Nat.Prime (35 - (2 ^ 6 + 11 * 2 ^ y)) ∧ (35 - (2 ^ 6 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_18_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 6) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 35 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (35 - (2 ^ x + 11 * 2 ^ y)) ∧ (35 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_18_eq_zero_x1 y hy1 hy2
  · exact summand_18_eq_zero_x2 y hy1 hy2
  · exact summand_18_eq_zero_x3 y hy1 hy2
  · exact summand_18_eq_zero_x4 y hy1 hy2
  · exact summand_18_eq_zero_x5 y hy1 hy2
  · exact summand_18_eq_zero_x6 y hy1 hy2

theorem a_eq_zero_18 : a 18 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 6 at hx2
  change y ≤ 6 at hy2
  exact summand_18_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_21_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 41 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (41 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (41 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 41 > 2 ^ 1 + 11 * 2 ^ 1 := by decide
    have h_eq : 41 - (2 ^ 1 + 11 * 2 ^ 1) = 17 := by rfl
    have h_mod : 17 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 17 ∧ 17 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_21_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 41 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (41 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (41 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 41 > 2 ^ 2 + 11 * 2 ^ 1 := by decide
    have h_eq : 41 - (2 ^ 2 + 11 * 2 ^ 1) = 15 := by rfl
    have h_mod : 15 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 15 ∧ 15 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_21_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 41 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (41 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (41 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 41 > 2 ^ 3 + 11 * 2 ^ 1 := by decide
    have h_eq : 41 - (2 ^ 3 + 11 * 2 ^ 1) = 11 := by rfl
    have h_mod : 11 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 11 ∧ 11 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_21_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 41 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (41 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (41 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 41 > 2 ^ 4 + 11 * 2 ^ 1 := by decide
    have h_eq : 41 - (2 ^ 4 + 11 * 2 ^ 1) = 3 := by rfl
    have h_mod : 3 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 3 ∧ 3 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_21_eq_zero_x5 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 41 > 2 ^ 5 + 11 * 2 ^ y then
    if Nat.Prime (41 - (2 ^ 5 + 11 * 2 ^ y)) ∧ (41 - (2 ^ 5 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_21_eq_zero_x6 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 41 > 2 ^ 6 + 11 * 2 ^ y then
    if Nat.Prime (41 - (2 ^ 6 + 11 * 2 ^ y)) ∧ (41 - (2 ^ 6 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_21_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 6) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 41 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (41 - (2 ^ x + 11 * 2 ^ y)) ∧ (41 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_21_eq_zero_x1 y hy1 hy2
  · exact summand_21_eq_zero_x2 y hy1 hy2
  · exact summand_21_eq_zero_x3 y hy1 hy2
  · exact summand_21_eq_zero_x4 y hy1 hy2
  · exact summand_21_eq_zero_x5 y hy1 hy2
  · exact summand_21_eq_zero_x6 y hy1 hy2

theorem a_eq_zero_21 : a 21 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 6 at hx2
  change y ≤ 6 at hy2
  exact summand_21_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_24_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 47 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (47 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (47 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 47 > 2 ^ 1 + 11 * 2 ^ 1 := by decide
    have h_eq : 47 - (2 ^ 1 + 11 * 2 ^ 1) = 23 := by rfl
    have h_mod : 23 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 23 ∧ 23 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 47 > 2 ^ 1 + 11 * 2 ^ 2 := by decide
    have h_eq : 47 - (2 ^ 1 + 11 * 2 ^ 2) = 1 := by rfl
    have h_not_prime : ¬ Nat.Prime 1 := Nat.not_prime_one
    have h_and : ¬ (Nat.Prime 1 ∧ 1 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_24_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 47 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (47 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (47 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 47 > 2 ^ 2 + 11 * 2 ^ 1 := by decide
    have h_eq : 47 - (2 ^ 2 + 11 * 2 ^ 1) = 21 := by rfl
    have h_mod : 21 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 21 ∧ 21 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_24_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 47 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (47 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (47 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 47 > 2 ^ 3 + 11 * 2 ^ 1 := by decide
    have h_eq : 47 - (2 ^ 3 + 11 * 2 ^ 1) = 17 := by rfl
    have h_mod : 17 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 17 ∧ 17 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_24_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 47 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (47 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (47 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 47 > 2 ^ 4 + 11 * 2 ^ 1 := by decide
    have h_eq : 47 - (2 ^ 4 + 11 * 2 ^ 1) = 9 := by rfl
    have h_mod : 9 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 9 ∧ 9 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_24_eq_zero_x5 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 47 > 2 ^ 5 + 11 * 2 ^ y then
    if Nat.Prime (47 - (2 ^ 5 + 11 * 2 ^ y)) ∧ (47 - (2 ^ 5 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_24_eq_zero_x6 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 47 > 2 ^ 6 + 11 * 2 ^ y then
    if Nat.Prime (47 - (2 ^ 6 + 11 * 2 ^ y)) ∧ (47 - (2 ^ 6 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl

lemma summand_24_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 6) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
  (if 47 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (47 - (2 ^ x + 11 * 2 ^ y)) ∧ (47 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_24_eq_zero_x1 y hy1 hy2
  · exact summand_24_eq_zero_x2 y hy1 hy2
  · exact summand_24_eq_zero_x3 y hy1 hy2
  · exact summand_24_eq_zero_x4 y hy1 hy2
  · exact summand_24_eq_zero_x5 y hy1 hy2
  · exact summand_24_eq_zero_x6 y hy1 hy2

theorem a_eq_zero_24 : a 24 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 6 at hx2
  change y ≤ 6 at hy2
  exact summand_24_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_51_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 7) :
  (if 101 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (101 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (101 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 101 > 2 ^ 1 + 11 * 2 ^ 1 := by decide
    have h_eq : 101 - (2 ^ 1 + 11 * 2 ^ 1) = 77 := by rfl
    have h_mod : 77 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 77 ∧ 77 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 101 > 2 ^ 1 + 11 * 2 ^ 2 := by decide
    have h_eq : 101 - (2 ^ 1 + 11 * 2 ^ 2) = 55 := by rfl
    have h_not_prime : ¬ Nat.Prime 55 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 55 ∧ 55 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 101 > 2 ^ 1 + 11 * 2 ^ 3 := by decide
    have h_eq : 101 - (2 ^ 1 + 11 * 2 ^ 3) = 11 := by rfl
    have h_mod : 11 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 11 ∧ 11 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl

lemma summand_51_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 7) :
  (if 101 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (101 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (101 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 101 > 2 ^ 2 + 11 * 2 ^ 1 := by decide
    have h_eq : 101 - (2 ^ 2 + 11 * 2 ^ 1) = 75 := by rfl
    have h_mod : 75 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 75 ∧ 75 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 101 > 2 ^ 2 + 11 * 2 ^ 2 := by decide
    have h_eq : 101 - (2 ^ 2 + 11 * 2 ^ 2) = 53 := by rfl
    have h_mod : 53 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 53 ∧ 53 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 101 > 2 ^ 2 + 11 * 2 ^ 3 := by decide
    have h_eq : 101 - (2 ^ 2 + 11 * 2 ^ 3) = 9 := by rfl
    have h_mod : 9 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 9 ∧ 9 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl

lemma summand_51_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 7) :
  (if 101 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (101 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (101 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 101 > 2 ^ 3 + 11 * 2 ^ 1 := by decide
    have h_eq : 101 - (2 ^ 3 + 11 * 2 ^ 1) = 71 := by rfl
    have h_mod : 71 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 71 ∧ 71 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 101 > 2 ^ 3 + 11 * 2 ^ 2 := by decide
    have h_eq : 101 - (2 ^ 3 + 11 * 2 ^ 2) = 49 := by rfl
    have h_not_prime : ¬ Nat.Prime 49 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 49 ∧ 49 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 101 > 2 ^ 3 + 11 * 2 ^ 3 := by decide
    have h_eq : 101 - (2 ^ 3 + 11 * 2 ^ 3) = 5 := by rfl
    have h_mod : 5 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 5 ∧ 5 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl

lemma summand_51_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 7) :
  (if 101 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (101 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (101 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 101 > 2 ^ 4 + 11 * 2 ^ 1 := by decide
    have h_eq : 101 - (2 ^ 4 + 11 * 2 ^ 1) = 63 := by rfl
    have h_mod : 63 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 63 ∧ 63 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 101 > 2 ^ 4 + 11 * 2 ^ 2 := by decide
    have h_eq : 101 - (2 ^ 4 + 11 * 2 ^ 2) = 41 := by rfl
    have h_mod : 41 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 41 ∧ 41 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl

lemma summand_51_eq_zero_x5 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 7) :
  (if 101 > 2 ^ 5 + 11 * 2 ^ y then
    if Nat.Prime (101 - (2 ^ 5 + 11 * 2 ^ y)) ∧ (101 - (2 ^ 5 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 101 > 2 ^ 5 + 11 * 2 ^ 1 := by decide
    have h_eq : 101 - (2 ^ 5 + 11 * 2 ^ 1) = 47 := by rfl
    have h_mod : 47 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 47 ∧ 47 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 101 > 2 ^ 5 + 11 * 2 ^ 2 := by decide
    have h_eq : 101 - (2 ^ 5 + 11 * 2 ^ 2) = 25 := by rfl
    have h_not_prime : ¬ Nat.Prime 25 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 25 ∧ 25 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl

lemma summand_51_eq_zero_x6 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 7) :
  (if 101 > 2 ^ 6 + 11 * 2 ^ y then
    if Nat.Prime (101 - (2 ^ 6 + 11 * 2 ^ y)) ∧ (101 - (2 ^ 6 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 101 > 2 ^ 6 + 11 * 2 ^ 1 := by decide
    have h_eq : 101 - (2 ^ 6 + 11 * 2 ^ 1) = 15 := by rfl
    have h_mod : 15 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 15 ∧ 15 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl

lemma summand_51_eq_zero_x7 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 7) :
  (if 101 > 2 ^ 7 + 11 * 2 ^ y then
    if Nat.Prime (101 - (2 ^ 7 + 11 * 2 ^ y)) ∧ (101 - (2 ^ 7 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl

lemma summand_51_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 7) (hy1 : 1 ≤ y) (hy2 : y ≤ 7) :
  (if 101 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (101 - (2 ^ x + 11 * 2 ^ y)) ∧ (101 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_51_eq_zero_x1 y hy1 hy2
  · exact summand_51_eq_zero_x2 y hy1 hy2
  · exact summand_51_eq_zero_x3 y hy1 hy2
  · exact summand_51_eq_zero_x4 y hy1 hy2
  · exact summand_51_eq_zero_x5 y hy1 hy2
  · exact summand_51_eq_zero_x6 y hy1 hy2
  · exact summand_51_eq_zero_x7 y hy1 hy2

theorem a_eq_zero_51 : a 51 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 7 at hx2
  change y ≤ 7 at hy2
  exact summand_51_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_84_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 8) :
  (if 167 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (167 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (167 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 167 > 2 ^ 1 + 11 * 2 ^ 1 := by decide
    have h_eq : 167 - (2 ^ 1 + 11 * 2 ^ 1) = 143 := by rfl
    have h_mod : 143 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 143 ∧ 143 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 167 > 2 ^ 1 + 11 * 2 ^ 2 := by decide
    have h_eq : 167 - (2 ^ 1 + 11 * 2 ^ 2) = 121 := by rfl
    have h_not_prime : ¬ Nat.Prime 121 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 11)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 121 ∧ 121 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 167 > 2 ^ 1 + 11 * 2 ^ 3 := by decide
    have h_eq : 167 - (2 ^ 1 + 11 * 2 ^ 3) = 77 := by rfl
    have h_mod : 77 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 77 ∧ 77 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl
  · -- y = 8
    rfl

lemma summand_84_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 8) :
  (if 167 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (167 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (167 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 167 > 2 ^ 2 + 11 * 2 ^ 1 := by decide
    have h_eq : 167 - (2 ^ 2 + 11 * 2 ^ 1) = 141 := by rfl
    have h_mod : 141 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 141 ∧ 141 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 167 > 2 ^ 2 + 11 * 2 ^ 2 := by decide
    have h_eq : 167 - (2 ^ 2 + 11 * 2 ^ 2) = 119 := by rfl
    have h_mod : 119 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119 ∧ 119 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 167 > 2 ^ 2 + 11 * 2 ^ 3 := by decide
    have h_eq : 167 - (2 ^ 2 + 11 * 2 ^ 3) = 75 := by rfl
    have h_mod : 75 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 75 ∧ 75 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl
  · -- y = 8
    rfl

lemma summand_84_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 8) :
  (if 167 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (167 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (167 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 167 > 2 ^ 3 + 11 * 2 ^ 1 := by decide
    have h_eq : 167 - (2 ^ 3 + 11 * 2 ^ 1) = 137 := by rfl
    have h_mod : 137 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 137 ∧ 137 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 167 > 2 ^ 3 + 11 * 2 ^ 2 := by decide
    have h_eq : 167 - (2 ^ 3 + 11 * 2 ^ 2) = 115 := by rfl
    have h_not_prime : ¬ Nat.Prime 115 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 115 ∧ 115 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 167 > 2 ^ 3 + 11 * 2 ^ 3 := by decide
    have h_eq : 167 - (2 ^ 3 + 11 * 2 ^ 3) = 71 := by rfl
    have h_mod : 71 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 71 ∧ 71 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl
  · -- y = 8
    rfl

lemma summand_84_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 8) :
  (if 167 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (167 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (167 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 167 > 2 ^ 4 + 11 * 2 ^ 1 := by decide
    have h_eq : 167 - (2 ^ 4 + 11 * 2 ^ 1) = 129 := by rfl
    have h_mod : 129 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 129 ∧ 129 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 167 > 2 ^ 4 + 11 * 2 ^ 2 := by decide
    have h_eq : 167 - (2 ^ 4 + 11 * 2 ^ 2) = 107 := by rfl
    have h_mod : 107 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 107 ∧ 107 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 167 > 2 ^ 4 + 11 * 2 ^ 3 := by decide
    have h_eq : 167 - (2 ^ 4 + 11 * 2 ^ 3) = 63 := by rfl
    have h_mod : 63 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 63 ∧ 63 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl
  · -- y = 8
    rfl

lemma summand_84_eq_zero_x5 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 8) :
  (if 167 > 2 ^ 5 + 11 * 2 ^ y then
    if Nat.Prime (167 - (2 ^ 5 + 11 * 2 ^ y)) ∧ (167 - (2 ^ 5 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 167 > 2 ^ 5 + 11 * 2 ^ 1 := by decide
    have h_eq : 167 - (2 ^ 5 + 11 * 2 ^ 1) = 113 := by rfl
    have h_mod : 113 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 113 ∧ 113 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 167 > 2 ^ 5 + 11 * 2 ^ 2 := by decide
    have h_eq : 167 - (2 ^ 5 + 11 * 2 ^ 2) = 91 := by rfl
    have h_not_prime : ¬ Nat.Prime 91 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 91 ∧ 91 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 167 > 2 ^ 5 + 11 * 2 ^ 3 := by decide
    have h_eq : 167 - (2 ^ 5 + 11 * 2 ^ 3) = 47 := by rfl
    have h_mod : 47 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 47 ∧ 47 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl
  · -- y = 8
    rfl

lemma summand_84_eq_zero_x6 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 8) :
  (if 167 > 2 ^ 6 + 11 * 2 ^ y then
    if Nat.Prime (167 - (2 ^ 6 + 11 * 2 ^ y)) ∧ (167 - (2 ^ 6 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 167 > 2 ^ 6 + 11 * 2 ^ 1 := by decide
    have h_eq : 167 - (2 ^ 6 + 11 * 2 ^ 1) = 81 := by rfl
    have h_mod : 81 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 81 ∧ 81 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 167 > 2 ^ 6 + 11 * 2 ^ 2 := by decide
    have h_eq : 167 - (2 ^ 6 + 11 * 2 ^ 2) = 59 := by rfl
    have h_mod : 59 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 59 ∧ 59 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 167 > 2 ^ 6 + 11 * 2 ^ 3 := by decide
    have h_eq : 167 - (2 ^ 6 + 11 * 2 ^ 3) = 15 := by rfl
    have h_mod : 15 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 15 ∧ 15 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl
  · -- y = 8
    rfl

lemma summand_84_eq_zero_x7 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 8) :
  (if 167 > 2 ^ 7 + 11 * 2 ^ y then
    if Nat.Prime (167 - (2 ^ 7 + 11 * 2 ^ y)) ∧ (167 - (2 ^ 7 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 167 > 2 ^ 7 + 11 * 2 ^ 1 := by decide
    have h_eq : 167 - (2 ^ 7 + 11 * 2 ^ 1) = 17 := by rfl
    have h_mod : 17 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 17 ∧ 17 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl
  · -- y = 8
    rfl

lemma summand_84_eq_zero_x8 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 8) :
  (if 167 > 2 ^ 8 + 11 * 2 ^ y then
    if Nat.Prime (167 - (2 ^ 8 + 11 * 2 ^ y)) ∧ (167 - (2 ^ 8 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl
  · -- y = 8
    rfl

lemma summand_84_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (hy1 : 1 ≤ y) (hy2 : y ≤ 8) :
  (if 167 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (167 - (2 ^ x + 11 * 2 ^ y)) ∧ (167 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_84_eq_zero_x1 y hy1 hy2
  · exact summand_84_eq_zero_x2 y hy1 hy2
  · exact summand_84_eq_zero_x3 y hy1 hy2
  · exact summand_84_eq_zero_x4 y hy1 hy2
  · exact summand_84_eq_zero_x5 y hy1 hy2
  · exact summand_84_eq_zero_x6 y hy1 hy2
  · exact summand_84_eq_zero_x7 y hy1 hy2
  · exact summand_84_eq_zero_x8 y hy1 hy2

theorem a_eq_zero_84 : a 84 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 8 at hx2
  change y ≤ 8 at hy2
  exact summand_84_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_1011_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 11) :
  (if 2021 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (2021 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (2021 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 2021 > 2 ^ 1 + 11 * 2 ^ 1 := by decide
    have h_eq : 2021 - (2 ^ 1 + 11 * 2 ^ 1) = 1997 := by rfl
    have h_mod : 1997 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1997 ∧ 1997 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 2021 > 2 ^ 1 + 11 * 2 ^ 2 := by decide
    have h_eq : 2021 - (2 ^ 1 + 11 * 2 ^ 2) = 1975 := by rfl
    have h_not_prime : ¬ Nat.Prime 1975 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 1975 ∧ 1975 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 2021 > 2 ^ 1 + 11 * 2 ^ 3 := by decide
    have h_eq : 2021 - (2 ^ 1 + 11 * 2 ^ 3) = 1931 := by rfl
    have h_mod : 1931 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1931 ∧ 1931 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 2021 > 2 ^ 1 + 11 * 2 ^ 4 := by decide
    have h_eq : 2021 - (2 ^ 1 + 11 * 2 ^ 4) = 1843 := by rfl
    have h_not_prime : ¬ Nat.Prime 1843 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 19)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 1843 ∧ 1843 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 2021 > 2 ^ 1 + 11 * 2 ^ 5 := by decide
    have h_eq : 2021 - (2 ^ 1 + 11 * 2 ^ 5) = 1667 := by rfl
    have h_mod : 1667 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1667 ∧ 1667 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 2021 > 2 ^ 1 + 11 * 2 ^ 6 := by decide
    have h_eq : 2021 - (2 ^ 1 + 11 * 2 ^ 6) = 1315 := by rfl
    have h_not_prime : ¬ Nat.Prime 1315 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 1315 ∧ 1315 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 2021 > 2 ^ 1 + 11 * 2 ^ 7 := by decide
    have h_eq : 2021 - (2 ^ 1 + 11 * 2 ^ 7) = 611 := by rfl
    have h_mod : 611 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 611 ∧ 611 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    rfl
  · -- y = 9
    rfl
  · -- y = 10
    rfl
  · -- y = 11
    rfl

lemma summand_1011_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 11) :
  (if 2021 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (2021 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (2021 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 2021 > 2 ^ 2 + 11 * 2 ^ 1 := by decide
    have h_eq : 2021 - (2 ^ 2 + 11 * 2 ^ 1) = 1995 := by rfl
    have h_mod : 1995 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1995 ∧ 1995 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 2021 > 2 ^ 2 + 11 * 2 ^ 2 := by decide
    have h_eq : 2021 - (2 ^ 2 + 11 * 2 ^ 2) = 1973 := by rfl
    have h_mod : 1973 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1973 ∧ 1973 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 2021 > 2 ^ 2 + 11 * 2 ^ 3 := by decide
    have h_eq : 2021 - (2 ^ 2 + 11 * 2 ^ 3) = 1929 := by rfl
    have h_mod : 1929 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1929 ∧ 1929 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 2021 > 2 ^ 2 + 11 * 2 ^ 4 := by decide
    have h_eq : 2021 - (2 ^ 2 + 11 * 2 ^ 4) = 1841 := by rfl
    have h_mod : 1841 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1841 ∧ 1841 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 2021 > 2 ^ 2 + 11 * 2 ^ 5 := by decide
    have h_eq : 2021 - (2 ^ 2 + 11 * 2 ^ 5) = 1665 := by rfl
    have h_mod : 1665 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1665 ∧ 1665 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 2021 > 2 ^ 2 + 11 * 2 ^ 6 := by decide
    have h_eq : 2021 - (2 ^ 2 + 11 * 2 ^ 6) = 1313 := by rfl
    have h_mod : 1313 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1313 ∧ 1313 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 2021 > 2 ^ 2 + 11 * 2 ^ 7 := by decide
    have h_eq : 2021 - (2 ^ 2 + 11 * 2 ^ 7) = 609 := by rfl
    have h_mod : 609 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 609 ∧ 609 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    rfl
  · -- y = 9
    rfl
  · -- y = 10
    rfl
  · -- y = 11
    rfl

lemma summand_1011_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 11) :
  (if 2021 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (2021 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (2021 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 2021 > 2 ^ 3 + 11 * 2 ^ 1 := by decide
    have h_eq : 2021 - (2 ^ 3 + 11 * 2 ^ 1) = 1991 := by rfl
    have h_mod : 1991 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1991 ∧ 1991 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 2021 > 2 ^ 3 + 11 * 2 ^ 2 := by decide
    have h_eq : 2021 - (2 ^ 3 + 11 * 2 ^ 2) = 1969 := by rfl
    have h_not_prime : ¬ Nat.Prime 1969 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 11)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 1969 ∧ 1969 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 2021 > 2 ^ 3 + 11 * 2 ^ 3 := by decide
    have h_eq : 2021 - (2 ^ 3 + 11 * 2 ^ 3) = 1925 := by rfl
    have h_mod : 1925 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1925 ∧ 1925 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 2021 > 2 ^ 3 + 11 * 2 ^ 4 := by decide
    have h_eq : 2021 - (2 ^ 3 + 11 * 2 ^ 4) = 1837 := by rfl
    have h_not_prime : ¬ Nat.Prime 1837 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 11)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 1837 ∧ 1837 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 2021 > 2 ^ 3 + 11 * 2 ^ 5 := by decide
    have h_eq : 2021 - (2 ^ 3 + 11 * 2 ^ 5) = 1661 := by rfl
    have h_mod : 1661 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1661 ∧ 1661 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 2021 > 2 ^ 3 + 11 * 2 ^ 6 := by decide
    have h_eq : 2021 - (2 ^ 3 + 11 * 2 ^ 6) = 1309 := by rfl
    have h_not_prime : ¬ Nat.Prime 1309 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 1309 ∧ 1309 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 2021 > 2 ^ 3 + 11 * 2 ^ 7 := by decide
    have h_eq : 2021 - (2 ^ 3 + 11 * 2 ^ 7) = 605 := by rfl
    have h_mod : 605 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 605 ∧ 605 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    rfl
  · -- y = 9
    rfl
  · -- y = 10
    rfl
  · -- y = 11
    rfl

lemma summand_1011_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 11) :
  (if 2021 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (2021 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (2021 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 2021 > 2 ^ 4 + 11 * 2 ^ 1 := by decide
    have h_eq : 2021 - (2 ^ 4 + 11 * 2 ^ 1) = 1983 := by rfl
    have h_mod : 1983 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1983 ∧ 1983 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 2021 > 2 ^ 4 + 11 * 2 ^ 2 := by decide
    have h_eq : 2021 - (2 ^ 4 + 11 * 2 ^ 2) = 1961 := by rfl
    have h_mod : 1961 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1961 ∧ 1961 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 2021 > 2 ^ 4 + 11 * 2 ^ 3 := by decide
    have h_eq : 2021 - (2 ^ 4 + 11 * 2 ^ 3) = 1917 := by rfl
    have h_mod : 1917 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1917 ∧ 1917 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 2021 > 2 ^ 4 + 11 * 2 ^ 4 := by decide
    have h_eq : 2021 - (2 ^ 4 + 11 * 2 ^ 4) = 1829 := by rfl
    have h_mod : 1829 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1829 ∧ 1829 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 2021 > 2 ^ 4 + 11 * 2 ^ 5 := by decide
    have h_eq : 2021 - (2 ^ 4 + 11 * 2 ^ 5) = 1653 := by rfl
    have h_mod : 1653 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1653 ∧ 1653 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 2021 > 2 ^ 4 + 11 * 2 ^ 6 := by decide
    have h_eq : 2021 - (2 ^ 4 + 11 * 2 ^ 6) = 1301 := by rfl
    have h_mod : 1301 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1301 ∧ 1301 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 2021 > 2 ^ 4 + 11 * 2 ^ 7 := by decide
    have h_eq : 2021 - (2 ^ 4 + 11 * 2 ^ 7) = 597 := by rfl
    have h_mod : 597 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 597 ∧ 597 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    rfl
  · -- y = 9
    rfl
  · -- y = 10
    rfl
  · -- y = 11
    rfl

lemma summand_1011_eq_zero_x5 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 11) :
  (if 2021 > 2 ^ 5 + 11 * 2 ^ y then
    if Nat.Prime (2021 - (2 ^ 5 + 11 * 2 ^ y)) ∧ (2021 - (2 ^ 5 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 2021 > 2 ^ 5 + 11 * 2 ^ 1 := by decide
    have h_eq : 2021 - (2 ^ 5 + 11 * 2 ^ 1) = 1967 := by rfl
    have h_mod : 1967 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1967 ∧ 1967 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 2021 > 2 ^ 5 + 11 * 2 ^ 2 := by decide
    have h_eq : 2021 - (2 ^ 5 + 11 * 2 ^ 2) = 1945 := by rfl
    have h_not_prime : ¬ Nat.Prime 1945 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 1945 ∧ 1945 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 2021 > 2 ^ 5 + 11 * 2 ^ 3 := by decide
    have h_eq : 2021 - (2 ^ 5 + 11 * 2 ^ 3) = 1901 := by rfl
    have h_mod : 1901 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1901 ∧ 1901 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 2021 > 2 ^ 5 + 11 * 2 ^ 4 := by decide
    have h_eq : 2021 - (2 ^ 5 + 11 * 2 ^ 4) = 1813 := by rfl
    have h_not_prime : ¬ Nat.Prime 1813 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 1813 ∧ 1813 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 2021 > 2 ^ 5 + 11 * 2 ^ 5 := by decide
    have h_eq : 2021 - (2 ^ 5 + 11 * 2 ^ 5) = 1637 := by rfl
    have h_mod : 1637 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1637 ∧ 1637 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 2021 > 2 ^ 5 + 11 * 2 ^ 6 := by decide
    have h_eq : 2021 - (2 ^ 5 + 11 * 2 ^ 6) = 1285 := by rfl
    have h_not_prime : ¬ Nat.Prime 1285 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 1285 ∧ 1285 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 2021 > 2 ^ 5 + 11 * 2 ^ 7 := by decide
    have h_eq : 2021 - (2 ^ 5 + 11 * 2 ^ 7) = 581 := by rfl
    have h_mod : 581 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 581 ∧ 581 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    rfl
  · -- y = 9
    rfl
  · -- y = 10
    rfl
  · -- y = 11
    rfl

lemma summand_1011_eq_zero_x6 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 11) :
  (if 2021 > 2 ^ 6 + 11 * 2 ^ y then
    if Nat.Prime (2021 - (2 ^ 6 + 11 * 2 ^ y)) ∧ (2021 - (2 ^ 6 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 2021 > 2 ^ 6 + 11 * 2 ^ 1 := by decide
    have h_eq : 2021 - (2 ^ 6 + 11 * 2 ^ 1) = 1935 := by rfl
    have h_mod : 1935 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1935 ∧ 1935 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 2021 > 2 ^ 6 + 11 * 2 ^ 2 := by decide
    have h_eq : 2021 - (2 ^ 6 + 11 * 2 ^ 2) = 1913 := by rfl
    have h_mod : 1913 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1913 ∧ 1913 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 2021 > 2 ^ 6 + 11 * 2 ^ 3 := by decide
    have h_eq : 2021 - (2 ^ 6 + 11 * 2 ^ 3) = 1869 := by rfl
    have h_mod : 1869 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1869 ∧ 1869 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 2021 > 2 ^ 6 + 11 * 2 ^ 4 := by decide
    have h_eq : 2021 - (2 ^ 6 + 11 * 2 ^ 4) = 1781 := by rfl
    have h_mod : 1781 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1781 ∧ 1781 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 2021 > 2 ^ 6 + 11 * 2 ^ 5 := by decide
    have h_eq : 2021 - (2 ^ 6 + 11 * 2 ^ 5) = 1605 := by rfl
    have h_mod : 1605 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1605 ∧ 1605 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 2021 > 2 ^ 6 + 11 * 2 ^ 6 := by decide
    have h_eq : 2021 - (2 ^ 6 + 11 * 2 ^ 6) = 1253 := by rfl
    have h_mod : 1253 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1253 ∧ 1253 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 2021 > 2 ^ 6 + 11 * 2 ^ 7 := by decide
    have h_eq : 2021 - (2 ^ 6 + 11 * 2 ^ 7) = 549 := by rfl
    have h_mod : 549 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 549 ∧ 549 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    rfl
  · -- y = 9
    rfl
  · -- y = 10
    rfl
  · -- y = 11
    rfl

lemma summand_1011_eq_zero_x7 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 11) :
  (if 2021 > 2 ^ 7 + 11 * 2 ^ y then
    if Nat.Prime (2021 - (2 ^ 7 + 11 * 2 ^ y)) ∧ (2021 - (2 ^ 7 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 2021 > 2 ^ 7 + 11 * 2 ^ 1 := by decide
    have h_eq : 2021 - (2 ^ 7 + 11 * 2 ^ 1) = 1871 := by rfl
    have h_mod : 1871 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1871 ∧ 1871 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 2021 > 2 ^ 7 + 11 * 2 ^ 2 := by decide
    have h_eq : 2021 - (2 ^ 7 + 11 * 2 ^ 2) = 1849 := by rfl
    have h_not_prime : ¬ Nat.Prime 1849 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 43)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 1849 ∧ 1849 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 2021 > 2 ^ 7 + 11 * 2 ^ 3 := by decide
    have h_eq : 2021 - (2 ^ 7 + 11 * 2 ^ 3) = 1805 := by rfl
    have h_mod : 1805 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1805 ∧ 1805 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 2021 > 2 ^ 7 + 11 * 2 ^ 4 := by decide
    have h_eq : 2021 - (2 ^ 7 + 11 * 2 ^ 4) = 1717 := by rfl
    have h_not_prime : ¬ Nat.Prime 1717 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 17)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 1717 ∧ 1717 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 2021 > 2 ^ 7 + 11 * 2 ^ 5 := by decide
    have h_eq : 2021 - (2 ^ 7 + 11 * 2 ^ 5) = 1541 := by rfl
    have h_mod : 1541 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1541 ∧ 1541 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 2021 > 2 ^ 7 + 11 * 2 ^ 6 := by decide
    have h_eq : 2021 - (2 ^ 7 + 11 * 2 ^ 6) = 1189 := by rfl
    have h_not_prime : ¬ Nat.Prime 1189 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 29)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 1189 ∧ 1189 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 2021 > 2 ^ 7 + 11 * 2 ^ 7 := by decide
    have h_eq : 2021 - (2 ^ 7 + 11 * 2 ^ 7) = 485 := by rfl
    have h_mod : 485 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 485 ∧ 485 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    rfl
  · -- y = 9
    rfl
  · -- y = 10
    rfl
  · -- y = 11
    rfl

lemma summand_1011_eq_zero_x8 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 11) :
  (if 2021 > 2 ^ 8 + 11 * 2 ^ y then
    if Nat.Prime (2021 - (2 ^ 8 + 11 * 2 ^ y)) ∧ (2021 - (2 ^ 8 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 2021 > 2 ^ 8 + 11 * 2 ^ 1 := by decide
    have h_eq : 2021 - (2 ^ 8 + 11 * 2 ^ 1) = 1743 := by rfl
    have h_mod : 1743 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1743 ∧ 1743 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 2021 > 2 ^ 8 + 11 * 2 ^ 2 := by decide
    have h_eq : 2021 - (2 ^ 8 + 11 * 2 ^ 2) = 1721 := by rfl
    have h_mod : 1721 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1721 ∧ 1721 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 2021 > 2 ^ 8 + 11 * 2 ^ 3 := by decide
    have h_eq : 2021 - (2 ^ 8 + 11 * 2 ^ 3) = 1677 := by rfl
    have h_mod : 1677 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1677 ∧ 1677 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 2021 > 2 ^ 8 + 11 * 2 ^ 4 := by decide
    have h_eq : 2021 - (2 ^ 8 + 11 * 2 ^ 4) = 1589 := by rfl
    have h_mod : 1589 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1589 ∧ 1589 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 2021 > 2 ^ 8 + 11 * 2 ^ 5 := by decide
    have h_eq : 2021 - (2 ^ 8 + 11 * 2 ^ 5) = 1413 := by rfl
    have h_mod : 1413 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1413 ∧ 1413 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 2021 > 2 ^ 8 + 11 * 2 ^ 6 := by decide
    have h_eq : 2021 - (2 ^ 8 + 11 * 2 ^ 6) = 1061 := by rfl
    have h_mod : 1061 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1061 ∧ 1061 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 2021 > 2 ^ 8 + 11 * 2 ^ 7 := by decide
    have h_eq : 2021 - (2 ^ 8 + 11 * 2 ^ 7) = 357 := by rfl
    have h_mod : 357 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 357 ∧ 357 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    rfl
  · -- y = 9
    rfl
  · -- y = 10
    rfl
  · -- y = 11
    rfl

lemma summand_1011_eq_zero_x9 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 11) :
  (if 2021 > 2 ^ 9 + 11 * 2 ^ y then
    if Nat.Prime (2021 - (2 ^ 9 + 11 * 2 ^ y)) ∧ (2021 - (2 ^ 9 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 2021 > 2 ^ 9 + 11 * 2 ^ 1 := by decide
    have h_eq : 2021 - (2 ^ 9 + 11 * 2 ^ 1) = 1487 := by rfl
    have h_mod : 1487 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1487 ∧ 1487 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 2021 > 2 ^ 9 + 11 * 2 ^ 2 := by decide
    have h_eq : 2021 - (2 ^ 9 + 11 * 2 ^ 2) = 1465 := by rfl
    have h_not_prime : ¬ Nat.Prime 1465 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 1465 ∧ 1465 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 2021 > 2 ^ 9 + 11 * 2 ^ 3 := by decide
    have h_eq : 2021 - (2 ^ 9 + 11 * 2 ^ 3) = 1421 := by rfl
    have h_mod : 1421 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1421 ∧ 1421 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 2021 > 2 ^ 9 + 11 * 2 ^ 4 := by decide
    have h_eq : 2021 - (2 ^ 9 + 11 * 2 ^ 4) = 1333 := by rfl
    have h_not_prime : ¬ Nat.Prime 1333 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 31)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 1333 ∧ 1333 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 2021 > 2 ^ 9 + 11 * 2 ^ 5 := by decide
    have h_eq : 2021 - (2 ^ 9 + 11 * 2 ^ 5) = 1157 := by rfl
    have h_mod : 1157 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 1157 ∧ 1157 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 2021 > 2 ^ 9 + 11 * 2 ^ 6 := by decide
    have h_eq : 2021 - (2 ^ 9 + 11 * 2 ^ 6) = 805 := by rfl
    have h_not_prime : ¬ Nat.Prime 805 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 805 ∧ 805 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 2021 > 2 ^ 9 + 11 * 2 ^ 7 := by decide
    have h_eq : 2021 - (2 ^ 9 + 11 * 2 ^ 7) = 101 := by rfl
    have h_mod : 101 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 101 ∧ 101 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    rfl
  · -- y = 9
    rfl
  · -- y = 10
    rfl
  · -- y = 11
    rfl

lemma summand_1011_eq_zero_x10 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 11) :
  (if 2021 > 2 ^ 10 + 11 * 2 ^ y then
    if Nat.Prime (2021 - (2 ^ 10 + 11 * 2 ^ y)) ∧ (2021 - (2 ^ 10 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 2021 > 2 ^ 10 + 11 * 2 ^ 1 := by decide
    have h_eq : 2021 - (2 ^ 10 + 11 * 2 ^ 1) = 975 := by rfl
    have h_mod : 975 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 975 ∧ 975 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 2021 > 2 ^ 10 + 11 * 2 ^ 2 := by decide
    have h_eq : 2021 - (2 ^ 10 + 11 * 2 ^ 2) = 953 := by rfl
    have h_mod : 953 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 953 ∧ 953 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 2021 > 2 ^ 10 + 11 * 2 ^ 3 := by decide
    have h_eq : 2021 - (2 ^ 10 + 11 * 2 ^ 3) = 909 := by rfl
    have h_mod : 909 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 909 ∧ 909 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 2021 > 2 ^ 10 + 11 * 2 ^ 4 := by decide
    have h_eq : 2021 - (2 ^ 10 + 11 * 2 ^ 4) = 821 := by rfl
    have h_mod : 821 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 821 ∧ 821 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 2021 > 2 ^ 10 + 11 * 2 ^ 5 := by decide
    have h_eq : 2021 - (2 ^ 10 + 11 * 2 ^ 5) = 645 := by rfl
    have h_mod : 645 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 645 ∧ 645 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 2021 > 2 ^ 10 + 11 * 2 ^ 6 := by decide
    have h_eq : 2021 - (2 ^ 10 + 11 * 2 ^ 6) = 293 := by rfl
    have h_mod : 293 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 293 ∧ 293 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    rfl
  · -- y = 8
    rfl
  · -- y = 9
    rfl
  · -- y = 10
    rfl
  · -- y = 11
    rfl

lemma summand_1011_eq_zero_x11 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 11) :
  (if 2021 > 2 ^ 11 + 11 * 2 ^ y then
    if Nat.Prime (2021 - (2 ^ 11 + 11 * 2 ^ y)) ∧ (2021 - (2 ^ 11 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl
  · -- y = 8
    rfl
  · -- y = 9
    rfl
  · -- y = 10
    rfl
  · -- y = 11
    rfl

lemma summand_1011_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 11) (hy1 : 1 ≤ y) (hy2 : y ≤ 11) :
  (if 2021 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (2021 - (2 ^ x + 11 * 2 ^ y)) ∧ (2021 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_1011_eq_zero_x1 y hy1 hy2
  · exact summand_1011_eq_zero_x2 y hy1 hy2
  · exact summand_1011_eq_zero_x3 y hy1 hy2
  · exact summand_1011_eq_zero_x4 y hy1 hy2
  · exact summand_1011_eq_zero_x5 y hy1 hy2
  · exact summand_1011_eq_zero_x6 y hy1 hy2
  · exact summand_1011_eq_zero_x7 y hy1 hy2
  · exact summand_1011_eq_zero_x8 y hy1 hy2
  · exact summand_1011_eq_zero_x9 y hy1 hy2
  · exact summand_1011_eq_zero_x10 y hy1 hy2
  · exact summand_1011_eq_zero_x11 y hy1 hy2

theorem a_eq_zero_1011 : a 1011 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 11 at hx2
  change y ≤ 11 at hy2
  exact summand_1011_eq_zero x y hx1 hx2 hy1 hy2

lemma summand_59586_eq_zero_x1 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 1 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 1 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 1 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 119171 > 2 ^ 1 + 11 * 2 ^ 1 := by decide
    have h_eq : 119171 - (2 ^ 1 + 11 * 2 ^ 1) = 119147 := by rfl
    have h_mod : 119147 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119147 ∧ 119147 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 119171 > 2 ^ 1 + 11 * 2 ^ 2 := by decide
    have h_eq : 119171 - (2 ^ 1 + 11 * 2 ^ 2) = 119125 := by rfl
    have h_not_prime : ¬ Nat.Prime 119125 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 119125 ∧ 119125 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 119171 > 2 ^ 1 + 11 * 2 ^ 3 := by decide
    have h_eq : 119171 - (2 ^ 1 + 11 * 2 ^ 3) = 119081 := by rfl
    have h_mod : 119081 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119081 ∧ 119081 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 119171 > 2 ^ 1 + 11 * 2 ^ 4 := by decide
    have h_eq : 119171 - (2 ^ 1 + 11 * 2 ^ 4) = 118993 := by rfl
    have h_not_prime : ¬ Nat.Prime 118993 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 118993 ∧ 118993 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 119171 > 2 ^ 1 + 11 * 2 ^ 5 := by decide
    have h_eq : 119171 - (2 ^ 1 + 11 * 2 ^ 5) = 118817 := by rfl
    have h_mod : 118817 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118817 ∧ 118817 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 119171 > 2 ^ 1 + 11 * 2 ^ 6 := by decide
    have h_eq : 119171 - (2 ^ 1 + 11 * 2 ^ 6) = 118465 := by rfl
    have h_not_prime : ¬ Nat.Prime 118465 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 118465 ∧ 118465 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 119171 > 2 ^ 1 + 11 * 2 ^ 7 := by decide
    have h_eq : 119171 - (2 ^ 1 + 11 * 2 ^ 7) = 117761 := by rfl
    have h_mod : 117761 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 117761 ∧ 117761 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    have h_gt : 119171 > 2 ^ 1 + 11 * 2 ^ 8 := by decide
    have h_eq : 119171 - (2 ^ 1 + 11 * 2 ^ 8) = 116353 := by rfl
    have h_not_prime : ¬ Nat.Prime 116353 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 307)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 116353 ∧ 116353 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 9
    have h_gt : 119171 > 2 ^ 1 + 11 * 2 ^ 9 := by decide
    have h_eq : 119171 - (2 ^ 1 + 11 * 2 ^ 9) = 113537 := by rfl
    have h_mod : 113537 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 113537 ∧ 113537 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 10
    have h_gt : 119171 > 2 ^ 1 + 11 * 2 ^ 10 := by decide
    have h_eq : 119171 - (2 ^ 1 + 11 * 2 ^ 10) = 107905 := by rfl
    have h_not_prime : ¬ Nat.Prime 107905 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 107905 ∧ 107905 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 11
    have h_gt : 119171 > 2 ^ 1 + 11 * 2 ^ 11 := by decide
    have h_eq : 119171 - (2 ^ 1 + 11 * 2 ^ 11) = 96641 := by rfl
    have h_mod : 96641 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 96641 ∧ 96641 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 12
    have h_gt : 119171 > 2 ^ 1 + 11 * 2 ^ 12 := by decide
    have h_eq : 119171 - (2 ^ 1 + 11 * 2 ^ 12) = 74113 := by rfl
    have h_not_prime : ¬ Nat.Prime 74113 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 13)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 74113 ∧ 74113 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 13
    have h_gt : 119171 > 2 ^ 1 + 11 * 2 ^ 13 := by decide
    have h_eq : 119171 - (2 ^ 1 + 11 * 2 ^ 13) = 29057 := by rfl
    have h_mod : 29057 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 29057 ∧ 29057 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero_x2 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 2 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 2 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 2 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 119171 > 2 ^ 2 + 11 * 2 ^ 1 := by decide
    have h_eq : 119171 - (2 ^ 2 + 11 * 2 ^ 1) = 119145 := by rfl
    have h_mod : 119145 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119145 ∧ 119145 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 119171 > 2 ^ 2 + 11 * 2 ^ 2 := by decide
    have h_eq : 119171 - (2 ^ 2 + 11 * 2 ^ 2) = 119123 := by rfl
    have h_mod : 119123 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119123 ∧ 119123 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 119171 > 2 ^ 2 + 11 * 2 ^ 3 := by decide
    have h_eq : 119171 - (2 ^ 2 + 11 * 2 ^ 3) = 119079 := by rfl
    have h_mod : 119079 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119079 ∧ 119079 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 119171 > 2 ^ 2 + 11 * 2 ^ 4 := by decide
    have h_eq : 119171 - (2 ^ 2 + 11 * 2 ^ 4) = 118991 := by rfl
    have h_mod : 118991 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118991 ∧ 118991 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 119171 > 2 ^ 2 + 11 * 2 ^ 5 := by decide
    have h_eq : 119171 - (2 ^ 2 + 11 * 2 ^ 5) = 118815 := by rfl
    have h_mod : 118815 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118815 ∧ 118815 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 119171 > 2 ^ 2 + 11 * 2 ^ 6 := by decide
    have h_eq : 119171 - (2 ^ 2 + 11 * 2 ^ 6) = 118463 := by rfl
    have h_mod : 118463 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118463 ∧ 118463 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 119171 > 2 ^ 2 + 11 * 2 ^ 7 := by decide
    have h_eq : 119171 - (2 ^ 2 + 11 * 2 ^ 7) = 117759 := by rfl
    have h_mod : 117759 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 117759 ∧ 117759 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    have h_gt : 119171 > 2 ^ 2 + 11 * 2 ^ 8 := by decide
    have h_eq : 119171 - (2 ^ 2 + 11 * 2 ^ 8) = 116351 := by rfl
    have h_mod : 116351 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 116351 ∧ 116351 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 9
    have h_gt : 119171 > 2 ^ 2 + 11 * 2 ^ 9 := by decide
    have h_eq : 119171 - (2 ^ 2 + 11 * 2 ^ 9) = 113535 := by rfl
    have h_mod : 113535 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 113535 ∧ 113535 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 10
    have h_gt : 119171 > 2 ^ 2 + 11 * 2 ^ 10 := by decide
    have h_eq : 119171 - (2 ^ 2 + 11 * 2 ^ 10) = 107903 := by rfl
    have h_mod : 107903 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 107903 ∧ 107903 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 11
    have h_gt : 119171 > 2 ^ 2 + 11 * 2 ^ 11 := by decide
    have h_eq : 119171 - (2 ^ 2 + 11 * 2 ^ 11) = 96639 := by rfl
    have h_mod : 96639 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 96639 ∧ 96639 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 12
    have h_gt : 119171 > 2 ^ 2 + 11 * 2 ^ 12 := by decide
    have h_eq : 119171 - (2 ^ 2 + 11 * 2 ^ 12) = 74111 := by rfl
    have h_mod : 74111 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 74111 ∧ 74111 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 13
    have h_gt : 119171 > 2 ^ 2 + 11 * 2 ^ 13 := by decide
    have h_eq : 119171 - (2 ^ 2 + 11 * 2 ^ 13) = 29055 := by rfl
    have h_mod : 29055 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 29055 ∧ 29055 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero_x3 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 3 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 3 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 3 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 119171 > 2 ^ 3 + 11 * 2 ^ 1 := by decide
    have h_eq : 119171 - (2 ^ 3 + 11 * 2 ^ 1) = 119141 := by rfl
    have h_mod : 119141 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119141 ∧ 119141 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 119171 > 2 ^ 3 + 11 * 2 ^ 2 := by decide
    have h_eq : 119171 - (2 ^ 3 + 11 * 2 ^ 2) = 119119 := by rfl
    have h_not_prime : ¬ Nat.Prime 119119 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 119119 ∧ 119119 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 119171 > 2 ^ 3 + 11 * 2 ^ 3 := by decide
    have h_eq : 119171 - (2 ^ 3 + 11 * 2 ^ 3) = 119075 := by rfl
    have h_mod : 119075 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119075 ∧ 119075 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 119171 > 2 ^ 3 + 11 * 2 ^ 4 := by decide
    have h_eq : 119171 - (2 ^ 3 + 11 * 2 ^ 4) = 118987 := by rfl
    have h_not_prime : ¬ Nat.Prime 118987 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 11)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 118987 ∧ 118987 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 119171 > 2 ^ 3 + 11 * 2 ^ 5 := by decide
    have h_eq : 119171 - (2 ^ 3 + 11 * 2 ^ 5) = 118811 := by rfl
    have h_mod : 118811 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118811 ∧ 118811 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 119171 > 2 ^ 3 + 11 * 2 ^ 6 := by decide
    have h_eq : 119171 - (2 ^ 3 + 11 * 2 ^ 6) = 118459 := by rfl
    have h_not_prime : ¬ Nat.Prime 118459 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 11)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 118459 ∧ 118459 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 119171 > 2 ^ 3 + 11 * 2 ^ 7 := by decide
    have h_eq : 119171 - (2 ^ 3 + 11 * 2 ^ 7) = 117755 := by rfl
    have h_mod : 117755 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 117755 ∧ 117755 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    have h_gt : 119171 > 2 ^ 3 + 11 * 2 ^ 8 := by decide
    have h_eq : 119171 - (2 ^ 3 + 11 * 2 ^ 8) = 116347 := by rfl
    have h_not_prime : ¬ Nat.Prime 116347 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 116347 ∧ 116347 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 9
    have h_gt : 119171 > 2 ^ 3 + 11 * 2 ^ 9 := by decide
    have h_eq : 119171 - (2 ^ 3 + 11 * 2 ^ 9) = 113531 := by rfl
    have h_mod : 113531 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 113531 ∧ 113531 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 10
    have h_gt : 119171 > 2 ^ 3 + 11 * 2 ^ 10 := by decide
    have h_eq : 119171 - (2 ^ 3 + 11 * 2 ^ 10) = 107899 := by rfl
    have h_not_prime : ¬ Nat.Prime 107899 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 11)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 107899 ∧ 107899 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 11
    have h_gt : 119171 > 2 ^ 3 + 11 * 2 ^ 11 := by decide
    have h_eq : 119171 - (2 ^ 3 + 11 * 2 ^ 11) = 96635 := by rfl
    have h_mod : 96635 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 96635 ∧ 96635 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 12
    have h_gt : 119171 > 2 ^ 3 + 11 * 2 ^ 12 := by decide
    have h_eq : 119171 - (2 ^ 3 + 11 * 2 ^ 12) = 74107 := by rfl
    have h_not_prime : ¬ Nat.Prime 74107 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 11)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 74107 ∧ 74107 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 13
    have h_gt : 119171 > 2 ^ 3 + 11 * 2 ^ 13 := by decide
    have h_eq : 119171 - (2 ^ 3 + 11 * 2 ^ 13) = 29051 := by rfl
    have h_mod : 29051 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 29051 ∧ 29051 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero_x4 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 4 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 4 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 4 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 119171 > 2 ^ 4 + 11 * 2 ^ 1 := by decide
    have h_eq : 119171 - (2 ^ 4 + 11 * 2 ^ 1) = 119133 := by rfl
    have h_mod : 119133 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119133 ∧ 119133 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 119171 > 2 ^ 4 + 11 * 2 ^ 2 := by decide
    have h_eq : 119171 - (2 ^ 4 + 11 * 2 ^ 2) = 119111 := by rfl
    have h_mod : 119111 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119111 ∧ 119111 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 119171 > 2 ^ 4 + 11 * 2 ^ 3 := by decide
    have h_eq : 119171 - (2 ^ 4 + 11 * 2 ^ 3) = 119067 := by rfl
    have h_mod : 119067 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119067 ∧ 119067 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 119171 > 2 ^ 4 + 11 * 2 ^ 4 := by decide
    have h_eq : 119171 - (2 ^ 4 + 11 * 2 ^ 4) = 118979 := by rfl
    have h_mod : 118979 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118979 ∧ 118979 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 119171 > 2 ^ 4 + 11 * 2 ^ 5 := by decide
    have h_eq : 119171 - (2 ^ 4 + 11 * 2 ^ 5) = 118803 := by rfl
    have h_mod : 118803 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118803 ∧ 118803 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 119171 > 2 ^ 4 + 11 * 2 ^ 6 := by decide
    have h_eq : 119171 - (2 ^ 4 + 11 * 2 ^ 6) = 118451 := by rfl
    have h_mod : 118451 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118451 ∧ 118451 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 119171 > 2 ^ 4 + 11 * 2 ^ 7 := by decide
    have h_eq : 119171 - (2 ^ 4 + 11 * 2 ^ 7) = 117747 := by rfl
    have h_mod : 117747 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 117747 ∧ 117747 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    have h_gt : 119171 > 2 ^ 4 + 11 * 2 ^ 8 := by decide
    have h_eq : 119171 - (2 ^ 4 + 11 * 2 ^ 8) = 116339 := by rfl
    have h_mod : 116339 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 116339 ∧ 116339 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 9
    have h_gt : 119171 > 2 ^ 4 + 11 * 2 ^ 9 := by decide
    have h_eq : 119171 - (2 ^ 4 + 11 * 2 ^ 9) = 113523 := by rfl
    have h_mod : 113523 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 113523 ∧ 113523 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 10
    have h_gt : 119171 > 2 ^ 4 + 11 * 2 ^ 10 := by decide
    have h_eq : 119171 - (2 ^ 4 + 11 * 2 ^ 10) = 107891 := by rfl
    have h_mod : 107891 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 107891 ∧ 107891 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 11
    have h_gt : 119171 > 2 ^ 4 + 11 * 2 ^ 11 := by decide
    have h_eq : 119171 - (2 ^ 4 + 11 * 2 ^ 11) = 96627 := by rfl
    have h_mod : 96627 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 96627 ∧ 96627 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 12
    have h_gt : 119171 > 2 ^ 4 + 11 * 2 ^ 12 := by decide
    have h_eq : 119171 - (2 ^ 4 + 11 * 2 ^ 12) = 74099 := by rfl
    have h_mod : 74099 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 74099 ∧ 74099 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 13
    have h_gt : 119171 > 2 ^ 4 + 11 * 2 ^ 13 := by decide
    have h_eq : 119171 - (2 ^ 4 + 11 * 2 ^ 13) = 29043 := by rfl
    have h_mod : 29043 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 29043 ∧ 29043 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero_x5 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 5 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 5 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 5 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 119171 > 2 ^ 5 + 11 * 2 ^ 1 := by decide
    have h_eq : 119171 - (2 ^ 5 + 11 * 2 ^ 1) = 119117 := by rfl
    have h_mod : 119117 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119117 ∧ 119117 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 119171 > 2 ^ 5 + 11 * 2 ^ 2 := by decide
    have h_eq : 119171 - (2 ^ 5 + 11 * 2 ^ 2) = 119095 := by rfl
    have h_not_prime : ¬ Nat.Prime 119095 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 119095 ∧ 119095 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 119171 > 2 ^ 5 + 11 * 2 ^ 3 := by decide
    have h_eq : 119171 - (2 ^ 5 + 11 * 2 ^ 3) = 119051 := by rfl
    have h_mod : 119051 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119051 ∧ 119051 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 119171 > 2 ^ 5 + 11 * 2 ^ 4 := by decide
    have h_eq : 119171 - (2 ^ 5 + 11 * 2 ^ 4) = 118963 := by rfl
    have h_not_prime : ¬ Nat.Prime 118963 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 13)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 118963 ∧ 118963 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 119171 > 2 ^ 5 + 11 * 2 ^ 5 := by decide
    have h_eq : 119171 - (2 ^ 5 + 11 * 2 ^ 5) = 118787 := by rfl
    have h_mod : 118787 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118787 ∧ 118787 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 119171 > 2 ^ 5 + 11 * 2 ^ 6 := by decide
    have h_eq : 119171 - (2 ^ 5 + 11 * 2 ^ 6) = 118435 := by rfl
    have h_not_prime : ¬ Nat.Prime 118435 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 118435 ∧ 118435 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 119171 > 2 ^ 5 + 11 * 2 ^ 7 := by decide
    have h_eq : 119171 - (2 ^ 5 + 11 * 2 ^ 7) = 117731 := by rfl
    have h_mod : 117731 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 117731 ∧ 117731 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    have h_gt : 119171 > 2 ^ 5 + 11 * 2 ^ 8 := by decide
    have h_eq : 119171 - (2 ^ 5 + 11 * 2 ^ 8) = 116323 := by rfl
    have h_not_prime : ¬ Nat.Prime 116323 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 89)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 116323 ∧ 116323 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 9
    have h_gt : 119171 > 2 ^ 5 + 11 * 2 ^ 9 := by decide
    have h_eq : 119171 - (2 ^ 5 + 11 * 2 ^ 9) = 113507 := by rfl
    have h_mod : 113507 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 113507 ∧ 113507 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 10
    have h_gt : 119171 > 2 ^ 5 + 11 * 2 ^ 10 := by decide
    have h_eq : 119171 - (2 ^ 5 + 11 * 2 ^ 10) = 107875 := by rfl
    have h_not_prime : ¬ Nat.Prime 107875 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 107875 ∧ 107875 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 11
    have h_gt : 119171 > 2 ^ 5 + 11 * 2 ^ 11 := by decide
    have h_eq : 119171 - (2 ^ 5 + 11 * 2 ^ 11) = 96611 := by rfl
    have h_mod : 96611 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 96611 ∧ 96611 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 12
    have h_gt : 119171 > 2 ^ 5 + 11 * 2 ^ 12 := by decide
    have h_eq : 119171 - (2 ^ 5 + 11 * 2 ^ 12) = 74083 := by rfl
    have h_not_prime : ¬ Nat.Prime 74083 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 23)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 74083 ∧ 74083 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 13
    have h_gt : 119171 > 2 ^ 5 + 11 * 2 ^ 13 := by decide
    have h_eq : 119171 - (2 ^ 5 + 11 * 2 ^ 13) = 29027 := by rfl
    have h_mod : 29027 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 29027 ∧ 29027 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero_x6 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 6 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 6 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 6 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 119171 > 2 ^ 6 + 11 * 2 ^ 1 := by decide
    have h_eq : 119171 - (2 ^ 6 + 11 * 2 ^ 1) = 119085 := by rfl
    have h_mod : 119085 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119085 ∧ 119085 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 119171 > 2 ^ 6 + 11 * 2 ^ 2 := by decide
    have h_eq : 119171 - (2 ^ 6 + 11 * 2 ^ 2) = 119063 := by rfl
    have h_mod : 119063 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119063 ∧ 119063 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 119171 > 2 ^ 6 + 11 * 2 ^ 3 := by decide
    have h_eq : 119171 - (2 ^ 6 + 11 * 2 ^ 3) = 119019 := by rfl
    have h_mod : 119019 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119019 ∧ 119019 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 119171 > 2 ^ 6 + 11 * 2 ^ 4 := by decide
    have h_eq : 119171 - (2 ^ 6 + 11 * 2 ^ 4) = 118931 := by rfl
    have h_mod : 118931 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118931 ∧ 118931 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 119171 > 2 ^ 6 + 11 * 2 ^ 5 := by decide
    have h_eq : 119171 - (2 ^ 6 + 11 * 2 ^ 5) = 118755 := by rfl
    have h_mod : 118755 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118755 ∧ 118755 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 119171 > 2 ^ 6 + 11 * 2 ^ 6 := by decide
    have h_eq : 119171 - (2 ^ 6 + 11 * 2 ^ 6) = 118403 := by rfl
    have h_mod : 118403 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118403 ∧ 118403 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 119171 > 2 ^ 6 + 11 * 2 ^ 7 := by decide
    have h_eq : 119171 - (2 ^ 6 + 11 * 2 ^ 7) = 117699 := by rfl
    have h_mod : 117699 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 117699 ∧ 117699 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    have h_gt : 119171 > 2 ^ 6 + 11 * 2 ^ 8 := by decide
    have h_eq : 119171 - (2 ^ 6 + 11 * 2 ^ 8) = 116291 := by rfl
    have h_mod : 116291 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 116291 ∧ 116291 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 9
    have h_gt : 119171 > 2 ^ 6 + 11 * 2 ^ 9 := by decide
    have h_eq : 119171 - (2 ^ 6 + 11 * 2 ^ 9) = 113475 := by rfl
    have h_mod : 113475 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 113475 ∧ 113475 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 10
    have h_gt : 119171 > 2 ^ 6 + 11 * 2 ^ 10 := by decide
    have h_eq : 119171 - (2 ^ 6 + 11 * 2 ^ 10) = 107843 := by rfl
    have h_mod : 107843 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 107843 ∧ 107843 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 11
    have h_gt : 119171 > 2 ^ 6 + 11 * 2 ^ 11 := by decide
    have h_eq : 119171 - (2 ^ 6 + 11 * 2 ^ 11) = 96579 := by rfl
    have h_mod : 96579 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 96579 ∧ 96579 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 12
    have h_gt : 119171 > 2 ^ 6 + 11 * 2 ^ 12 := by decide
    have h_eq : 119171 - (2 ^ 6 + 11 * 2 ^ 12) = 74051 := by rfl
    have h_mod : 74051 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 74051 ∧ 74051 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 13
    have h_gt : 119171 > 2 ^ 6 + 11 * 2 ^ 13 := by decide
    have h_eq : 119171 - (2 ^ 6 + 11 * 2 ^ 13) = 28995 := by rfl
    have h_mod : 28995 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 28995 ∧ 28995 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero_x7 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 7 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 7 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 7 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 119171 > 2 ^ 7 + 11 * 2 ^ 1 := by decide
    have h_eq : 119171 - (2 ^ 7 + 11 * 2 ^ 1) = 119021 := by rfl
    have h_mod : 119021 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 119021 ∧ 119021 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 119171 > 2 ^ 7 + 11 * 2 ^ 2 := by decide
    have h_eq : 119171 - (2 ^ 7 + 11 * 2 ^ 2) = 118999 := by rfl
    have h_not_prime : ¬ Nat.Prime 118999 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 127)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 118999 ∧ 118999 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 119171 > 2 ^ 7 + 11 * 2 ^ 3 := by decide
    have h_eq : 119171 - (2 ^ 7 + 11 * 2 ^ 3) = 118955 := by rfl
    have h_mod : 118955 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118955 ∧ 118955 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 119171 > 2 ^ 7 + 11 * 2 ^ 4 := by decide
    have h_eq : 119171 - (2 ^ 7 + 11 * 2 ^ 4) = 118867 := by rfl
    have h_not_prime : ¬ Nat.Prime 118867 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 118867 ∧ 118867 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 119171 > 2 ^ 7 + 11 * 2 ^ 5 := by decide
    have h_eq : 119171 - (2 ^ 7 + 11 * 2 ^ 5) = 118691 := by rfl
    have h_mod : 118691 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118691 ∧ 118691 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 119171 > 2 ^ 7 + 11 * 2 ^ 6 := by decide
    have h_eq : 119171 - (2 ^ 7 + 11 * 2 ^ 6) = 118339 := by rfl
    have h_not_prime : ¬ Nat.Prime 118339 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 13)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 118339 ∧ 118339 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 119171 > 2 ^ 7 + 11 * 2 ^ 7 := by decide
    have h_eq : 119171 - (2 ^ 7 + 11 * 2 ^ 7) = 117635 := by rfl
    have h_mod : 117635 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 117635 ∧ 117635 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    have h_gt : 119171 > 2 ^ 7 + 11 * 2 ^ 8 := by decide
    have h_eq : 119171 - (2 ^ 7 + 11 * 2 ^ 8) = 116227 := by rfl
    have h_not_prime : ¬ Nat.Prime 116227 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 71)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 116227 ∧ 116227 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 9
    have h_gt : 119171 > 2 ^ 7 + 11 * 2 ^ 9 := by decide
    have h_eq : 119171 - (2 ^ 7 + 11 * 2 ^ 9) = 113411 := by rfl
    have h_mod : 113411 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 113411 ∧ 113411 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 10
    have h_gt : 119171 > 2 ^ 7 + 11 * 2 ^ 10 := by decide
    have h_eq : 119171 - (2 ^ 7 + 11 * 2 ^ 10) = 107779 := by rfl
    have h_not_prime : ¬ Nat.Prime 107779 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 107779 ∧ 107779 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 11
    have h_gt : 119171 > 2 ^ 7 + 11 * 2 ^ 11 := by decide
    have h_eq : 119171 - (2 ^ 7 + 11 * 2 ^ 11) = 96515 := by rfl
    have h_mod : 96515 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 96515 ∧ 96515 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 12
    have h_gt : 119171 > 2 ^ 7 + 11 * 2 ^ 12 := by decide
    have h_eq : 119171 - (2 ^ 7 + 11 * 2 ^ 12) = 73987 := by rfl
    have h_not_prime : ¬ Nat.Prime 73987 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 241)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 73987 ∧ 73987 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 13
    have h_gt : 119171 > 2 ^ 7 + 11 * 2 ^ 13 := by decide
    have h_eq : 119171 - (2 ^ 7 + 11 * 2 ^ 13) = 28931 := by rfl
    have h_mod : 28931 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 28931 ∧ 28931 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero_x8 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 8 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 8 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 8 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 119171 > 2 ^ 8 + 11 * 2 ^ 1 := by decide
    have h_eq : 119171 - (2 ^ 8 + 11 * 2 ^ 1) = 118893 := by rfl
    have h_mod : 118893 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118893 ∧ 118893 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 119171 > 2 ^ 8 + 11 * 2 ^ 2 := by decide
    have h_eq : 119171 - (2 ^ 8 + 11 * 2 ^ 2) = 118871 := by rfl
    have h_mod : 118871 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118871 ∧ 118871 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 119171 > 2 ^ 8 + 11 * 2 ^ 3 := by decide
    have h_eq : 119171 - (2 ^ 8 + 11 * 2 ^ 3) = 118827 := by rfl
    have h_mod : 118827 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118827 ∧ 118827 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 119171 > 2 ^ 8 + 11 * 2 ^ 4 := by decide
    have h_eq : 119171 - (2 ^ 8 + 11 * 2 ^ 4) = 118739 := by rfl
    have h_mod : 118739 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118739 ∧ 118739 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 119171 > 2 ^ 8 + 11 * 2 ^ 5 := by decide
    have h_eq : 119171 - (2 ^ 8 + 11 * 2 ^ 5) = 118563 := by rfl
    have h_mod : 118563 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118563 ∧ 118563 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 119171 > 2 ^ 8 + 11 * 2 ^ 6 := by decide
    have h_eq : 119171 - (2 ^ 8 + 11 * 2 ^ 6) = 118211 := by rfl
    have h_mod : 118211 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118211 ∧ 118211 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 119171 > 2 ^ 8 + 11 * 2 ^ 7 := by decide
    have h_eq : 119171 - (2 ^ 8 + 11 * 2 ^ 7) = 117507 := by rfl
    have h_mod : 117507 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 117507 ∧ 117507 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    have h_gt : 119171 > 2 ^ 8 + 11 * 2 ^ 8 := by decide
    have h_eq : 119171 - (2 ^ 8 + 11 * 2 ^ 8) = 116099 := by rfl
    have h_mod : 116099 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 116099 ∧ 116099 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 9
    have h_gt : 119171 > 2 ^ 8 + 11 * 2 ^ 9 := by decide
    have h_eq : 119171 - (2 ^ 8 + 11 * 2 ^ 9) = 113283 := by rfl
    have h_mod : 113283 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 113283 ∧ 113283 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 10
    have h_gt : 119171 > 2 ^ 8 + 11 * 2 ^ 10 := by decide
    have h_eq : 119171 - (2 ^ 8 + 11 * 2 ^ 10) = 107651 := by rfl
    have h_mod : 107651 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 107651 ∧ 107651 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 11
    have h_gt : 119171 > 2 ^ 8 + 11 * 2 ^ 11 := by decide
    have h_eq : 119171 - (2 ^ 8 + 11 * 2 ^ 11) = 96387 := by rfl
    have h_mod : 96387 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 96387 ∧ 96387 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 12
    have h_gt : 119171 > 2 ^ 8 + 11 * 2 ^ 12 := by decide
    have h_eq : 119171 - (2 ^ 8 + 11 * 2 ^ 12) = 73859 := by rfl
    have h_mod : 73859 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 73859 ∧ 73859 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 13
    have h_gt : 119171 > 2 ^ 8 + 11 * 2 ^ 13 := by decide
    have h_eq : 119171 - (2 ^ 8 + 11 * 2 ^ 13) = 28803 := by rfl
    have h_mod : 28803 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 28803 ∧ 28803 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero_x9 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 9 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 9 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 9 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 119171 > 2 ^ 9 + 11 * 2 ^ 1 := by decide
    have h_eq : 119171 - (2 ^ 9 + 11 * 2 ^ 1) = 118637 := by rfl
    have h_mod : 118637 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118637 ∧ 118637 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 119171 > 2 ^ 9 + 11 * 2 ^ 2 := by decide
    have h_eq : 119171 - (2 ^ 9 + 11 * 2 ^ 2) = 118615 := by rfl
    have h_not_prime : ¬ Nat.Prime 118615 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 118615 ∧ 118615 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 119171 > 2 ^ 9 + 11 * 2 ^ 3 := by decide
    have h_eq : 119171 - (2 ^ 9 + 11 * 2 ^ 3) = 118571 := by rfl
    have h_mod : 118571 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118571 ∧ 118571 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 119171 > 2 ^ 9 + 11 * 2 ^ 4 := by decide
    have h_eq : 119171 - (2 ^ 9 + 11 * 2 ^ 4) = 118483 := by rfl
    have h_not_prime : ¬ Nat.Prime 118483 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 109)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 118483 ∧ 118483 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 119171 > 2 ^ 9 + 11 * 2 ^ 5 := by decide
    have h_eq : 119171 - (2 ^ 9 + 11 * 2 ^ 5) = 118307 := by rfl
    have h_mod : 118307 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118307 ∧ 118307 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 119171 > 2 ^ 9 + 11 * 2 ^ 6 := by decide
    have h_eq : 119171 - (2 ^ 9 + 11 * 2 ^ 6) = 117955 := by rfl
    have h_not_prime : ¬ Nat.Prime 117955 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 117955 ∧ 117955 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 119171 > 2 ^ 9 + 11 * 2 ^ 7 := by decide
    have h_eq : 119171 - (2 ^ 9 + 11 * 2 ^ 7) = 117251 := by rfl
    have h_mod : 117251 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 117251 ∧ 117251 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    have h_gt : 119171 > 2 ^ 9 + 11 * 2 ^ 8 := by decide
    have h_eq : 119171 - (2 ^ 9 + 11 * 2 ^ 8) = 115843 := by rfl
    have h_not_prime : ¬ Nat.Prime 115843 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 115843 ∧ 115843 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 9
    have h_gt : 119171 > 2 ^ 9 + 11 * 2 ^ 9 := by decide
    have h_eq : 119171 - (2 ^ 9 + 11 * 2 ^ 9) = 113027 := by rfl
    have h_mod : 113027 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 113027 ∧ 113027 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 10
    have h_gt : 119171 > 2 ^ 9 + 11 * 2 ^ 10 := by decide
    have h_eq : 119171 - (2 ^ 9 + 11 * 2 ^ 10) = 107395 := by rfl
    have h_not_prime : ¬ Nat.Prime 107395 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 107395 ∧ 107395 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 11
    have h_gt : 119171 > 2 ^ 9 + 11 * 2 ^ 11 := by decide
    have h_eq : 119171 - (2 ^ 9 + 11 * 2 ^ 11) = 96131 := by rfl
    have h_mod : 96131 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 96131 ∧ 96131 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 12
    have h_gt : 119171 > 2 ^ 9 + 11 * 2 ^ 12 := by decide
    have h_eq : 119171 - (2 ^ 9 + 11 * 2 ^ 12) = 73603 := by rfl
    have h_not_prime : ¬ Nat.Prime 73603 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 89)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 73603 ∧ 73603 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 13
    have h_gt : 119171 > 2 ^ 9 + 11 * 2 ^ 13 := by decide
    have h_eq : 119171 - (2 ^ 9 + 11 * 2 ^ 13) = 28547 := by rfl
    have h_mod : 28547 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 28547 ∧ 28547 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero_x10 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 10 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 10 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 10 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 119171 > 2 ^ 10 + 11 * 2 ^ 1 := by decide
    have h_eq : 119171 - (2 ^ 10 + 11 * 2 ^ 1) = 118125 := by rfl
    have h_mod : 118125 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118125 ∧ 118125 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 119171 > 2 ^ 10 + 11 * 2 ^ 2 := by decide
    have h_eq : 119171 - (2 ^ 10 + 11 * 2 ^ 2) = 118103 := by rfl
    have h_mod : 118103 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118103 ∧ 118103 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 119171 > 2 ^ 10 + 11 * 2 ^ 3 := by decide
    have h_eq : 119171 - (2 ^ 10 + 11 * 2 ^ 3) = 118059 := by rfl
    have h_mod : 118059 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 118059 ∧ 118059 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 119171 > 2 ^ 10 + 11 * 2 ^ 4 := by decide
    have h_eq : 119171 - (2 ^ 10 + 11 * 2 ^ 4) = 117971 := by rfl
    have h_mod : 117971 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 117971 ∧ 117971 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 119171 > 2 ^ 10 + 11 * 2 ^ 5 := by decide
    have h_eq : 119171 - (2 ^ 10 + 11 * 2 ^ 5) = 117795 := by rfl
    have h_mod : 117795 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 117795 ∧ 117795 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 119171 > 2 ^ 10 + 11 * 2 ^ 6 := by decide
    have h_eq : 119171 - (2 ^ 10 + 11 * 2 ^ 6) = 117443 := by rfl
    have h_mod : 117443 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 117443 ∧ 117443 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 119171 > 2 ^ 10 + 11 * 2 ^ 7 := by decide
    have h_eq : 119171 - (2 ^ 10 + 11 * 2 ^ 7) = 116739 := by rfl
    have h_mod : 116739 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 116739 ∧ 116739 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    have h_gt : 119171 > 2 ^ 10 + 11 * 2 ^ 8 := by decide
    have h_eq : 119171 - (2 ^ 10 + 11 * 2 ^ 8) = 115331 := by rfl
    have h_mod : 115331 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 115331 ∧ 115331 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 9
    have h_gt : 119171 > 2 ^ 10 + 11 * 2 ^ 9 := by decide
    have h_eq : 119171 - (2 ^ 10 + 11 * 2 ^ 9) = 112515 := by rfl
    have h_mod : 112515 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 112515 ∧ 112515 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 10
    have h_gt : 119171 > 2 ^ 10 + 11 * 2 ^ 10 := by decide
    have h_eq : 119171 - (2 ^ 10 + 11 * 2 ^ 10) = 106883 := by rfl
    have h_mod : 106883 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 106883 ∧ 106883 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 11
    have h_gt : 119171 > 2 ^ 10 + 11 * 2 ^ 11 := by decide
    have h_eq : 119171 - (2 ^ 10 + 11 * 2 ^ 11) = 95619 := by rfl
    have h_mod : 95619 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 95619 ∧ 95619 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 12
    have h_gt : 119171 > 2 ^ 10 + 11 * 2 ^ 12 := by decide
    have h_eq : 119171 - (2 ^ 10 + 11 * 2 ^ 12) = 73091 := by rfl
    have h_mod : 73091 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 73091 ∧ 73091 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 13
    have h_gt : 119171 > 2 ^ 10 + 11 * 2 ^ 13 := by decide
    have h_eq : 119171 - (2 ^ 10 + 11 * 2 ^ 13) = 28035 := by rfl
    have h_mod : 28035 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 28035 ∧ 28035 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero_x11 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 11 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 11 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 11 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 119171 > 2 ^ 11 + 11 * 2 ^ 1 := by decide
    have h_eq : 119171 - (2 ^ 11 + 11 * 2 ^ 1) = 117101 := by rfl
    have h_mod : 117101 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 117101 ∧ 117101 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 119171 > 2 ^ 11 + 11 * 2 ^ 2 := by decide
    have h_eq : 119171 - (2 ^ 11 + 11 * 2 ^ 2) = 117079 := by rfl
    have h_not_prime : ¬ Nat.Prime 117079 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 17)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 117079 ∧ 117079 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 119171 > 2 ^ 11 + 11 * 2 ^ 3 := by decide
    have h_eq : 119171 - (2 ^ 11 + 11 * 2 ^ 3) = 117035 := by rfl
    have h_mod : 117035 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 117035 ∧ 117035 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 119171 > 2 ^ 11 + 11 * 2 ^ 4 := by decide
    have h_eq : 119171 - (2 ^ 11 + 11 * 2 ^ 4) = 116947 := by rfl
    have h_not_prime : ¬ Nat.Prime 116947 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 83)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 116947 ∧ 116947 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 119171 > 2 ^ 11 + 11 * 2 ^ 5 := by decide
    have h_eq : 119171 - (2 ^ 11 + 11 * 2 ^ 5) = 116771 := by rfl
    have h_mod : 116771 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 116771 ∧ 116771 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 119171 > 2 ^ 11 + 11 * 2 ^ 6 := by decide
    have h_eq : 119171 - (2 ^ 11 + 11 * 2 ^ 6) = 116419 := by rfl
    have h_not_prime : ¬ Nat.Prime 116419 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 47)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 116419 ∧ 116419 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 119171 > 2 ^ 11 + 11 * 2 ^ 7 := by decide
    have h_eq : 119171 - (2 ^ 11 + 11 * 2 ^ 7) = 115715 := by rfl
    have h_mod : 115715 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 115715 ∧ 115715 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    have h_gt : 119171 > 2 ^ 11 + 11 * 2 ^ 8 := by decide
    have h_eq : 119171 - (2 ^ 11 + 11 * 2 ^ 8) = 114307 := by rfl
    have h_not_prime : ¬ Nat.Prime 114307 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 151)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 114307 ∧ 114307 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 9
    have h_gt : 119171 > 2 ^ 11 + 11 * 2 ^ 9 := by decide
    have h_eq : 119171 - (2 ^ 11 + 11 * 2 ^ 9) = 111491 := by rfl
    have h_mod : 111491 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 111491 ∧ 111491 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 10
    have h_gt : 119171 > 2 ^ 11 + 11 * 2 ^ 10 := by decide
    have h_eq : 119171 - (2 ^ 11 + 11 * 2 ^ 10) = 105859 := by rfl
    have h_not_prime : ¬ Nat.Prime 105859 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 13)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 105859 ∧ 105859 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 11
    have h_gt : 119171 > 2 ^ 11 + 11 * 2 ^ 11 := by decide
    have h_eq : 119171 - (2 ^ 11 + 11 * 2 ^ 11) = 94595 := by rfl
    have h_mod : 94595 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 94595 ∧ 94595 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 12
    have h_gt : 119171 > 2 ^ 11 + 11 * 2 ^ 12 := by decide
    have h_eq : 119171 - (2 ^ 11 + 11 * 2 ^ 12) = 72067 := by rfl
    have h_not_prime : ¬ Nat.Prime 72067 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 19)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 72067 ∧ 72067 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 13
    have h_gt : 119171 > 2 ^ 11 + 11 * 2 ^ 13 := by decide
    have h_eq : 119171 - (2 ^ 11 + 11 * 2 ^ 13) = 27011 := by rfl
    have h_mod : 27011 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 27011 ∧ 27011 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero_x12 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 12 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 12 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 12 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 119171 > 2 ^ 12 + 11 * 2 ^ 1 := by decide
    have h_eq : 119171 - (2 ^ 12 + 11 * 2 ^ 1) = 115053 := by rfl
    have h_mod : 115053 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 115053 ∧ 115053 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 119171 > 2 ^ 12 + 11 * 2 ^ 2 := by decide
    have h_eq : 119171 - (2 ^ 12 + 11 * 2 ^ 2) = 115031 := by rfl
    have h_mod : 115031 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 115031 ∧ 115031 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 119171 > 2 ^ 12 + 11 * 2 ^ 3 := by decide
    have h_eq : 119171 - (2 ^ 12 + 11 * 2 ^ 3) = 114987 := by rfl
    have h_mod : 114987 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 114987 ∧ 114987 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 119171 > 2 ^ 12 + 11 * 2 ^ 4 := by decide
    have h_eq : 119171 - (2 ^ 12 + 11 * 2 ^ 4) = 114899 := by rfl
    have h_mod : 114899 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 114899 ∧ 114899 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 119171 > 2 ^ 12 + 11 * 2 ^ 5 := by decide
    have h_eq : 119171 - (2 ^ 12 + 11 * 2 ^ 5) = 114723 := by rfl
    have h_mod : 114723 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 114723 ∧ 114723 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 119171 > 2 ^ 12 + 11 * 2 ^ 6 := by decide
    have h_eq : 119171 - (2 ^ 12 + 11 * 2 ^ 6) = 114371 := by rfl
    have h_mod : 114371 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 114371 ∧ 114371 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 119171 > 2 ^ 12 + 11 * 2 ^ 7 := by decide
    have h_eq : 119171 - (2 ^ 12 + 11 * 2 ^ 7) = 113667 := by rfl
    have h_mod : 113667 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 113667 ∧ 113667 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    have h_gt : 119171 > 2 ^ 12 + 11 * 2 ^ 8 := by decide
    have h_eq : 119171 - (2 ^ 12 + 11 * 2 ^ 8) = 112259 := by rfl
    have h_mod : 112259 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 112259 ∧ 112259 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 9
    have h_gt : 119171 > 2 ^ 12 + 11 * 2 ^ 9 := by decide
    have h_eq : 119171 - (2 ^ 12 + 11 * 2 ^ 9) = 109443 := by rfl
    have h_mod : 109443 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 109443 ∧ 109443 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 10
    have h_gt : 119171 > 2 ^ 12 + 11 * 2 ^ 10 := by decide
    have h_eq : 119171 - (2 ^ 12 + 11 * 2 ^ 10) = 103811 := by rfl
    have h_mod : 103811 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 103811 ∧ 103811 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 11
    have h_gt : 119171 > 2 ^ 12 + 11 * 2 ^ 11 := by decide
    have h_eq : 119171 - (2 ^ 12 + 11 * 2 ^ 11) = 92547 := by rfl
    have h_mod : 92547 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 92547 ∧ 92547 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 12
    have h_gt : 119171 > 2 ^ 12 + 11 * 2 ^ 12 := by decide
    have h_eq : 119171 - (2 ^ 12 + 11 * 2 ^ 12) = 70019 := by rfl
    have h_mod : 70019 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 70019 ∧ 70019 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 13
    have h_gt : 119171 > 2 ^ 12 + 11 * 2 ^ 13 := by decide
    have h_eq : 119171 - (2 ^ 12 + 11 * 2 ^ 13) = 24963 := by rfl
    have h_mod : 24963 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 24963 ∧ 24963 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero_x13 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 13 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 13 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 13 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 119171 > 2 ^ 13 + 11 * 2 ^ 1 := by decide
    have h_eq : 119171 - (2 ^ 13 + 11 * 2 ^ 1) = 110957 := by rfl
    have h_mod : 110957 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 110957 ∧ 110957 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 119171 > 2 ^ 13 + 11 * 2 ^ 2 := by decide
    have h_eq : 119171 - (2 ^ 13 + 11 * 2 ^ 2) = 110935 := by rfl
    have h_not_prime : ¬ Nat.Prime 110935 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 110935 ∧ 110935 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 119171 > 2 ^ 13 + 11 * 2 ^ 3 := by decide
    have h_eq : 119171 - (2 ^ 13 + 11 * 2 ^ 3) = 110891 := by rfl
    have h_mod : 110891 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 110891 ∧ 110891 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 119171 > 2 ^ 13 + 11 * 2 ^ 4 := by decide
    have h_eq : 119171 - (2 ^ 13 + 11 * 2 ^ 4) = 110803 := by rfl
    have h_not_prime : ¬ Nat.Prime 110803 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 110803 ∧ 110803 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 119171 > 2 ^ 13 + 11 * 2 ^ 5 := by decide
    have h_eq : 119171 - (2 ^ 13 + 11 * 2 ^ 5) = 110627 := by rfl
    have h_mod : 110627 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 110627 ∧ 110627 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 119171 > 2 ^ 13 + 11 * 2 ^ 6 := by decide
    have h_eq : 119171 - (2 ^ 13 + 11 * 2 ^ 6) = 110275 := by rfl
    have h_not_prime : ¬ Nat.Prime 110275 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 110275 ∧ 110275 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 119171 > 2 ^ 13 + 11 * 2 ^ 7 := by decide
    have h_eq : 119171 - (2 ^ 13 + 11 * 2 ^ 7) = 109571 := by rfl
    have h_mod : 109571 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 109571 ∧ 109571 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    have h_gt : 119171 > 2 ^ 13 + 11 * 2 ^ 8 := by decide
    have h_eq : 119171 - (2 ^ 13 + 11 * 2 ^ 8) = 108163 := by rfl
    have h_not_prime : ¬ Nat.Prime 108163 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 11)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 108163 ∧ 108163 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 9
    have h_gt : 119171 > 2 ^ 13 + 11 * 2 ^ 9 := by decide
    have h_eq : 119171 - (2 ^ 13 + 11 * 2 ^ 9) = 105347 := by rfl
    have h_mod : 105347 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 105347 ∧ 105347 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 10
    have h_gt : 119171 > 2 ^ 13 + 11 * 2 ^ 10 := by decide
    have h_eq : 119171 - (2 ^ 13 + 11 * 2 ^ 10) = 99715 := by rfl
    have h_not_prime : ¬ Nat.Prime 99715 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 99715 ∧ 99715 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 11
    have h_gt : 119171 > 2 ^ 13 + 11 * 2 ^ 11 := by decide
    have h_eq : 119171 - (2 ^ 13 + 11 * 2 ^ 11) = 88451 := by rfl
    have h_mod : 88451 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 88451 ∧ 88451 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 12
    have h_gt : 119171 > 2 ^ 13 + 11 * 2 ^ 12 := by decide
    have h_eq : 119171 - (2 ^ 13 + 11 * 2 ^ 12) = 65923 := by rfl
    have h_not_prime : ¬ Nat.Prime 65923 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 11)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 65923 ∧ 65923 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 13
    have h_gt : 119171 > 2 ^ 13 + 11 * 2 ^ 13 := by decide
    have h_eq : 119171 - (2 ^ 13 + 11 * 2 ^ 13) = 20867 := by rfl
    have h_mod : 20867 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 20867 ∧ 20867 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero_x14 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 14 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 14 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 14 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 119171 > 2 ^ 14 + 11 * 2 ^ 1 := by decide
    have h_eq : 119171 - (2 ^ 14 + 11 * 2 ^ 1) = 102765 := by rfl
    have h_mod : 102765 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 102765 ∧ 102765 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 119171 > 2 ^ 14 + 11 * 2 ^ 2 := by decide
    have h_eq : 119171 - (2 ^ 14 + 11 * 2 ^ 2) = 102743 := by rfl
    have h_mod : 102743 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 102743 ∧ 102743 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 119171 > 2 ^ 14 + 11 * 2 ^ 3 := by decide
    have h_eq : 119171 - (2 ^ 14 + 11 * 2 ^ 3) = 102699 := by rfl
    have h_mod : 102699 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 102699 ∧ 102699 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 119171 > 2 ^ 14 + 11 * 2 ^ 4 := by decide
    have h_eq : 119171 - (2 ^ 14 + 11 * 2 ^ 4) = 102611 := by rfl
    have h_mod : 102611 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 102611 ∧ 102611 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 119171 > 2 ^ 14 + 11 * 2 ^ 5 := by decide
    have h_eq : 119171 - (2 ^ 14 + 11 * 2 ^ 5) = 102435 := by rfl
    have h_mod : 102435 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 102435 ∧ 102435 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 119171 > 2 ^ 14 + 11 * 2 ^ 6 := by decide
    have h_eq : 119171 - (2 ^ 14 + 11 * 2 ^ 6) = 102083 := by rfl
    have h_mod : 102083 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 102083 ∧ 102083 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 119171 > 2 ^ 14 + 11 * 2 ^ 7 := by decide
    have h_eq : 119171 - (2 ^ 14 + 11 * 2 ^ 7) = 101379 := by rfl
    have h_mod : 101379 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 101379 ∧ 101379 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    have h_gt : 119171 > 2 ^ 14 + 11 * 2 ^ 8 := by decide
    have h_eq : 119171 - (2 ^ 14 + 11 * 2 ^ 8) = 99971 := by rfl
    have h_mod : 99971 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 99971 ∧ 99971 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 9
    have h_gt : 119171 > 2 ^ 14 + 11 * 2 ^ 9 := by decide
    have h_eq : 119171 - (2 ^ 14 + 11 * 2 ^ 9) = 97155 := by rfl
    have h_mod : 97155 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 97155 ∧ 97155 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 10
    have h_gt : 119171 > 2 ^ 14 + 11 * 2 ^ 10 := by decide
    have h_eq : 119171 - (2 ^ 14 + 11 * 2 ^ 10) = 91523 := by rfl
    have h_mod : 91523 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 91523 ∧ 91523 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 11
    have h_gt : 119171 > 2 ^ 14 + 11 * 2 ^ 11 := by decide
    have h_eq : 119171 - (2 ^ 14 + 11 * 2 ^ 11) = 80259 := by rfl
    have h_mod : 80259 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 80259 ∧ 80259 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 12
    have h_gt : 119171 > 2 ^ 14 + 11 * 2 ^ 12 := by decide
    have h_eq : 119171 - (2 ^ 14 + 11 * 2 ^ 12) = 57731 := by rfl
    have h_mod : 57731 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 57731 ∧ 57731 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 13
    have h_gt : 119171 > 2 ^ 14 + 11 * 2 ^ 13 := by decide
    have h_eq : 119171 - (2 ^ 14 + 11 * 2 ^ 13) = 12675 := by rfl
    have h_mod : 12675 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 12675 ∧ 12675 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero_x15 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 15 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 15 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 15 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 119171 > 2 ^ 15 + 11 * 2 ^ 1 := by decide
    have h_eq : 119171 - (2 ^ 15 + 11 * 2 ^ 1) = 86381 := by rfl
    have h_mod : 86381 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 86381 ∧ 86381 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 119171 > 2 ^ 15 + 11 * 2 ^ 2 := by decide
    have h_eq : 119171 - (2 ^ 15 + 11 * 2 ^ 2) = 86359 := by rfl
    have h_not_prime : ¬ Nat.Prime 86359 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 86359 ∧ 86359 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 119171 > 2 ^ 15 + 11 * 2 ^ 3 := by decide
    have h_eq : 119171 - (2 ^ 15 + 11 * 2 ^ 3) = 86315 := by rfl
    have h_mod : 86315 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 86315 ∧ 86315 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 119171 > 2 ^ 15 + 11 * 2 ^ 4 := by decide
    have h_eq : 119171 - (2 ^ 15 + 11 * 2 ^ 4) = 86227 := by rfl
    have h_not_prime : ¬ Nat.Prime 86227 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 23)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 86227 ∧ 86227 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 119171 > 2 ^ 15 + 11 * 2 ^ 5 := by decide
    have h_eq : 119171 - (2 ^ 15 + 11 * 2 ^ 5) = 86051 := by rfl
    have h_mod : 86051 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 86051 ∧ 86051 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 119171 > 2 ^ 15 + 11 * 2 ^ 6 := by decide
    have h_eq : 119171 - (2 ^ 15 + 11 * 2 ^ 6) = 85699 := by rfl
    have h_not_prime : ¬ Nat.Prime 85699 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 43)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 85699 ∧ 85699 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 119171 > 2 ^ 15 + 11 * 2 ^ 7 := by decide
    have h_eq : 119171 - (2 ^ 15 + 11 * 2 ^ 7) = 84995 := by rfl
    have h_mod : 84995 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 84995 ∧ 84995 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    have h_gt : 119171 > 2 ^ 15 + 11 * 2 ^ 8 := by decide
    have h_eq : 119171 - (2 ^ 15 + 11 * 2 ^ 8) = 83587 := by rfl
    have h_not_prime : ¬ Nat.Prime 83587 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 83587 ∧ 83587 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 9
    have h_gt : 119171 > 2 ^ 15 + 11 * 2 ^ 9 := by decide
    have h_eq : 119171 - (2 ^ 15 + 11 * 2 ^ 9) = 80771 := by rfl
    have h_mod : 80771 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 80771 ∧ 80771 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 10
    have h_gt : 119171 > 2 ^ 15 + 11 * 2 ^ 10 := by decide
    have h_eq : 119171 - (2 ^ 15 + 11 * 2 ^ 10) = 75139 := by rfl
    have h_not_prime : ¬ Nat.Prime 75139 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 29)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 75139 ∧ 75139 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 11
    have h_gt : 119171 > 2 ^ 15 + 11 * 2 ^ 11 := by decide
    have h_eq : 119171 - (2 ^ 15 + 11 * 2 ^ 11) = 63875 := by rfl
    have h_mod : 63875 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 63875 ∧ 63875 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 12
    have h_gt : 119171 > 2 ^ 15 + 11 * 2 ^ 12 := by decide
    have h_eq : 119171 - (2 ^ 15 + 11 * 2 ^ 12) = 41347 := by rfl
    have h_not_prime : ¬ Nat.Prime 41347 := by
      apply Nat.not_prime_of_dvd_of_lt (m := 173)
      · decide
      · decide
      · decide
    have h_and : ¬ (Nat.Prime 41347 ∧ 41347 % 6 = 1) := fun h => h_not_prime h.1
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 13
    rfl
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero_x16 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 16 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 16 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 16 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    have h_gt : 119171 > 2 ^ 16 + 11 * 2 ^ 1 := by decide
    have h_eq : 119171 - (2 ^ 16 + 11 * 2 ^ 1) = 53613 := by rfl
    have h_mod : 53613 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 53613 ∧ 53613 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 2
    have h_gt : 119171 > 2 ^ 16 + 11 * 2 ^ 2 := by decide
    have h_eq : 119171 - (2 ^ 16 + 11 * 2 ^ 2) = 53591 := by rfl
    have h_mod : 53591 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 53591 ∧ 53591 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 3
    have h_gt : 119171 > 2 ^ 16 + 11 * 2 ^ 3 := by decide
    have h_eq : 119171 - (2 ^ 16 + 11 * 2 ^ 3) = 53547 := by rfl
    have h_mod : 53547 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 53547 ∧ 53547 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 4
    have h_gt : 119171 > 2 ^ 16 + 11 * 2 ^ 4 := by decide
    have h_eq : 119171 - (2 ^ 16 + 11 * 2 ^ 4) = 53459 := by rfl
    have h_mod : 53459 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 53459 ∧ 53459 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 5
    have h_gt : 119171 > 2 ^ 16 + 11 * 2 ^ 5 := by decide
    have h_eq : 119171 - (2 ^ 16 + 11 * 2 ^ 5) = 53283 := by rfl
    have h_mod : 53283 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 53283 ∧ 53283 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 6
    have h_gt : 119171 > 2 ^ 16 + 11 * 2 ^ 6 := by decide
    have h_eq : 119171 - (2 ^ 16 + 11 * 2 ^ 6) = 52931 := by rfl
    have h_mod : 52931 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 52931 ∧ 52931 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 7
    have h_gt : 119171 > 2 ^ 16 + 11 * 2 ^ 7 := by decide
    have h_eq : 119171 - (2 ^ 16 + 11 * 2 ^ 7) = 52227 := by rfl
    have h_mod : 52227 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 52227 ∧ 52227 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 8
    have h_gt : 119171 > 2 ^ 16 + 11 * 2 ^ 8 := by decide
    have h_eq : 119171 - (2 ^ 16 + 11 * 2 ^ 8) = 50819 := by rfl
    have h_mod : 50819 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 50819 ∧ 50819 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 9
    have h_gt : 119171 > 2 ^ 16 + 11 * 2 ^ 9 := by decide
    have h_eq : 119171 - (2 ^ 16 + 11 * 2 ^ 9) = 48003 := by rfl
    have h_mod : 48003 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 48003 ∧ 48003 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 10
    have h_gt : 119171 > 2 ^ 16 + 11 * 2 ^ 10 := by decide
    have h_eq : 119171 - (2 ^ 16 + 11 * 2 ^ 10) = 42371 := by rfl
    have h_mod : 42371 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 42371 ∧ 42371 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 11
    have h_gt : 119171 > 2 ^ 16 + 11 * 2 ^ 11 := by decide
    have h_eq : 119171 - (2 ^ 16 + 11 * 2 ^ 11) = 31107 := by rfl
    have h_mod : 31107 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 31107 ∧ 31107 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 12
    have h_gt : 119171 > 2 ^ 16 + 11 * 2 ^ 12 := by decide
    have h_eq : 119171 - (2 ^ 16 + 11 * 2 ^ 12) = 8579 := by rfl
    have h_mod : 8579 % 6 ≠ 1 := by decide
    have h_and : ¬ (Nat.Prime 8579 ∧ 8579 % 6 = 1) := fun h => h_mod h.2
    rw [if_pos h_gt]
    rw [h_eq]
    rw [if_neg h_and]
  · -- y = 13
    rfl
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero_x17 (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ 17 + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ 17 + 11 * 2 ^ y)) ∧ (119171 - (2 ^ 17 + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases y
  · -- y = 1
    rfl
  · -- y = 2
    rfl
  · -- y = 3
    rfl
  · -- y = 4
    rfl
  · -- y = 5
    rfl
  · -- y = 6
    rfl
  · -- y = 7
    rfl
  · -- y = 8
    rfl
  · -- y = 9
    rfl
  · -- y = 10
    rfl
  · -- y = 11
    rfl
  · -- y = 12
    rfl
  · -- y = 13
    rfl
  · -- y = 14
    rfl
  · -- y = 15
    rfl
  · -- y = 16
    rfl
  · -- y = 17
    rfl

lemma summand_59586_eq_zero (x y : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 17) (hy1 : 1 ≤ y) (hy2 : y ≤ 17) :
  (if 119171 > 2 ^ x + 11 * 2 ^ y then
    if Nat.Prime (119171 - (2 ^ x + 11 * 2 ^ y)) ∧ (119171 - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0
   else 0) = 0 := by
  interval_cases x
  · exact summand_59586_eq_zero_x1 y hy1 hy2
  · exact summand_59586_eq_zero_x2 y hy1 hy2
  · exact summand_59586_eq_zero_x3 y hy1 hy2
  · exact summand_59586_eq_zero_x4 y hy1 hy2
  · exact summand_59586_eq_zero_x5 y hy1 hy2
  · exact summand_59586_eq_zero_x6 y hy1 hy2
  · exact summand_59586_eq_zero_x7 y hy1 hy2
  · exact summand_59586_eq_zero_x8 y hy1 hy2
  · exact summand_59586_eq_zero_x9 y hy1 hy2
  · exact summand_59586_eq_zero_x10 y hy1 hy2
  · exact summand_59586_eq_zero_x11 y hy1 hy2
  · exact summand_59586_eq_zero_x12 y hy1 hy2
  · exact summand_59586_eq_zero_x13 y hy1 hy2
  · exact summand_59586_eq_zero_x14 y hy1 hy2
  · exact summand_59586_eq_zero_x15 y hy1 hy2
  · exact summand_59586_eq_zero_x16 y hy1 hy2
  · exact summand_59586_eq_zero_x17 y hy1 hy2

theorem a_eq_zero_59586 : a 59586 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 17 at hx2
  change y ≤ 17 at hy2
  exact summand_59586_eq_zero x y hx1 hx2 hy1 hy2

theorem oeis_A157237_sun_conjecture : ∀ n : ℕ, n > 0 → (a n = 0 ↔ n ≤ 15 ∨ n = 18 ∨ n = 21 ∨ n = 24 ∨ n = 51 ∨ n = 84 ∨ n = 1011 ∨ n = 59586) := by
  intro n hn
  constructor
  · intro han
    -- The forward direction is mathematically unresolved (it is an open number theory conjecture).
    sorry
  · intro h_or
    rcases h_or with h | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · interval_cases n
      · exact a_eq_zero_1
      · exact a_eq_zero_2
      · exact a_eq_zero_3
      · exact a_eq_zero_4
      · exact a_eq_zero_5
      · exact a_eq_zero_6
      · exact a_eq_zero_7
      · exact a_eq_zero_8
      · exact a_eq_zero_9
      · exact a_eq_zero_10
      · exact a_eq_zero_11
      · exact a_eq_zero_12
      · exact a_eq_zero_13
      · exact a_eq_zero_14
      · exact a_eq_zero_15
    · exact a_eq_zero_18
    · exact a_eq_zero_21
    · exact a_eq_zero_24
    · exact a_eq_zero_51
    · exact a_eq_zero_84
    · exact a_eq_zero_1011
    · exact a_eq_zero_59586
