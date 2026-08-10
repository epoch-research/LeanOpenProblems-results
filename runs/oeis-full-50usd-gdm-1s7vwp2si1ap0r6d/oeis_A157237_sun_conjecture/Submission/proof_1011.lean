import FormalConjectures.Util.ProblemImports
open Nat

theorem a_eq_zero_1011 : a 1011 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 11 at hx2
  change y ≤ 11 at hy2
  interval_cases x
  · -- x = 1
    interval_cases y
    · -- y = 1
      rfl
    · -- y = 2
      have h_not_prime : ¬ Nat.Prime 1975 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 1975 ∧ 1975 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 1975 ∧ 1975 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 3
      rfl
    · -- y = 4
      have h_not_prime : ¬ Nat.Prime 1843 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 19)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 1843 ∧ 1843 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 1843 ∧ 1843 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 5
      rfl
    · -- y = 6
      have h_not_prime : ¬ Nat.Prime 1315 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 1315 ∧ 1315 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 1315 ∧ 1315 % 6 = 1 then 1 else 0) = 0
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
  · -- x = 2
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
  · -- x = 3
    interval_cases y
    · -- y = 1
      rfl
    · -- y = 2
      have h_not_prime : ¬ Nat.Prime 1969 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 11)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 1969 ∧ 1969 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 1969 ∧ 1969 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 3
      rfl
    · -- y = 4
      have h_not_prime : ¬ Nat.Prime 1837 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 11)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 1837 ∧ 1837 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 1837 ∧ 1837 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 5
      rfl
    · -- y = 6
      have h_not_prime : ¬ Nat.Prime 1309 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 7)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 1309 ∧ 1309 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 1309 ∧ 1309 % 6 = 1 then 1 else 0) = 0
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
  · -- x = 4
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
  · -- x = 5
    interval_cases y
    · -- y = 1
      rfl
    · -- y = 2
      have h_not_prime : ¬ Nat.Prime 1945 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 1945 ∧ 1945 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 1945 ∧ 1945 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 3
      rfl
    · -- y = 4
      have h_not_prime : ¬ Nat.Prime 1813 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 7)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 1813 ∧ 1813 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 1813 ∧ 1813 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 5
      rfl
    · -- y = 6
      have h_not_prime : ¬ Nat.Prime 1285 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 1285 ∧ 1285 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 1285 ∧ 1285 % 6 = 1 then 1 else 0) = 0
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
  · -- x = 6
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
  · -- x = 7
    interval_cases y
    · -- y = 1
      rfl
    · -- y = 2
      have h_not_prime : ¬ Nat.Prime 1849 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 43)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 1849 ∧ 1849 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 1849 ∧ 1849 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 3
      rfl
    · -- y = 4
      have h_not_prime : ¬ Nat.Prime 1717 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 17)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 1717 ∧ 1717 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 1717 ∧ 1717 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 5
      rfl
    · -- y = 6
      have h_not_prime : ¬ Nat.Prime 1189 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 29)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 1189 ∧ 1189 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 1189 ∧ 1189 % 6 = 1 then 1 else 0) = 0
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
  · -- x = 8
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
  · -- x = 9
    interval_cases y
    · -- y = 1
      rfl
    · -- y = 2
      have h_not_prime : ¬ Nat.Prime 1465 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 1465 ∧ 1465 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 1465 ∧ 1465 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 3
      rfl
    · -- y = 4
      have h_not_prime : ¬ Nat.Prime 1333 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 31)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 1333 ∧ 1333 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 1333 ∧ 1333 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 5
      rfl
    · -- y = 6
      have h_not_prime : ¬ Nat.Prime 805 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 805 ∧ 805 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 805 ∧ 805 % 6 = 1 then 1 else 0) = 0
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
  · -- x = 10
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
  · -- x = 11
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
