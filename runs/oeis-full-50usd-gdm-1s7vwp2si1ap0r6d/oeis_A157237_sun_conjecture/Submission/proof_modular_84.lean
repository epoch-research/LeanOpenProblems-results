import FormalConjectures.Util.ProblemImports
open Nat

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
