import FormalConjectures.Util.ProblemImports
open Nat

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
