import FormalConjectures.Util.ProblemImports
open Nat

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
