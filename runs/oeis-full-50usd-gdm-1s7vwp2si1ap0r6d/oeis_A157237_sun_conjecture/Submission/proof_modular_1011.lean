import FormalConjectures.Util.ProblemImports
open Nat

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
