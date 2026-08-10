import FormalConjectures.Util.ProblemImports
open Nat

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
