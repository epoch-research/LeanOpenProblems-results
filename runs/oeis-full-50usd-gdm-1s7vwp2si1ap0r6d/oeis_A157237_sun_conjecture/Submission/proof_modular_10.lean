import FormalConjectures.Util.ProblemImports
open Nat

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
