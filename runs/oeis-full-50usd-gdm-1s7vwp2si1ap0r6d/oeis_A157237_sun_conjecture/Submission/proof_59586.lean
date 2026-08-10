import FormalConjectures.Util.ProblemImports
open Nat

theorem a_eq_zero_59586 : a 59586 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 17 at hx2
  change y ≤ 17 at hy2
  interval_cases x
  · -- x = 1
    interval_cases y
    · -- y = 1
      rfl
    · -- y = 2
      have h_not_prime : ¬ Nat.Prime 119125 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 119125 ∧ 119125 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 119125 ∧ 119125 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 3
      rfl
    · -- y = 4
      have h_not_prime : ¬ Nat.Prime 118993 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 7)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 118993 ∧ 118993 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 118993 ∧ 118993 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 5
      rfl
    · -- y = 6
      have h_not_prime : ¬ Nat.Prime 118465 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 118465 ∧ 118465 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 118465 ∧ 118465 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 7
      rfl
    · -- y = 8
      have h_not_prime : ¬ Nat.Prime 116353 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 307)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 116353 ∧ 116353 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 116353 ∧ 116353 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 9
      rfl
    · -- y = 10
      have h_not_prime : ¬ Nat.Prime 107905 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 107905 ∧ 107905 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 107905 ∧ 107905 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 11
      rfl
    · -- y = 12
      have h_not_prime : ¬ Nat.Prime 74113 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 13)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 74113 ∧ 74113 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 74113 ∧ 74113 % 6 = 1 then 1 else 0) = 0
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
  · -- x = 3
    interval_cases y
    · -- y = 1
      rfl
    · -- y = 2
      have h_not_prime : ¬ Nat.Prime 119119 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 7)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 119119 ∧ 119119 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 119119 ∧ 119119 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 3
      rfl
    · -- y = 4
      have h_not_prime : ¬ Nat.Prime 118987 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 11)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 118987 ∧ 118987 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 118987 ∧ 118987 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 5
      rfl
    · -- y = 6
      have h_not_prime : ¬ Nat.Prime 118459 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 11)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 118459 ∧ 118459 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 118459 ∧ 118459 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 7
      rfl
    · -- y = 8
      have h_not_prime : ¬ Nat.Prime 116347 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 7)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 116347 ∧ 116347 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 116347 ∧ 116347 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 9
      rfl
    · -- y = 10
      have h_not_prime : ¬ Nat.Prime 107899 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 11)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 107899 ∧ 107899 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 107899 ∧ 107899 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 11
      rfl
    · -- y = 12
      have h_not_prime : ¬ Nat.Prime 74107 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 11)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 74107 ∧ 74107 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 74107 ∧ 74107 % 6 = 1 then 1 else 0) = 0
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
  · -- x = 5
    interval_cases y
    · -- y = 1
      rfl
    · -- y = 2
      have h_not_prime : ¬ Nat.Prime 119095 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 119095 ∧ 119095 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 119095 ∧ 119095 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 3
      rfl
    · -- y = 4
      have h_not_prime : ¬ Nat.Prime 118963 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 13)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 118963 ∧ 118963 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 118963 ∧ 118963 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 5
      rfl
    · -- y = 6
      have h_not_prime : ¬ Nat.Prime 118435 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 118435 ∧ 118435 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 118435 ∧ 118435 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 7
      rfl
    · -- y = 8
      have h_not_prime : ¬ Nat.Prime 116323 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 89)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 116323 ∧ 116323 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 116323 ∧ 116323 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 9
      rfl
    · -- y = 10
      have h_not_prime : ¬ Nat.Prime 107875 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 107875 ∧ 107875 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 107875 ∧ 107875 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 11
      rfl
    · -- y = 12
      have h_not_prime : ¬ Nat.Prime 74083 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 23)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 74083 ∧ 74083 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 74083 ∧ 74083 % 6 = 1 then 1 else 0) = 0
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
  · -- x = 7
    interval_cases y
    · -- y = 1
      rfl
    · -- y = 2
      have h_not_prime : ¬ Nat.Prime 118999 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 127)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 118999 ∧ 118999 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 118999 ∧ 118999 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 3
      rfl
    · -- y = 4
      have h_not_prime : ¬ Nat.Prime 118867 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 7)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 118867 ∧ 118867 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 118867 ∧ 118867 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 5
      rfl
    · -- y = 6
      have h_not_prime : ¬ Nat.Prime 118339 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 13)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 118339 ∧ 118339 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 118339 ∧ 118339 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 7
      rfl
    · -- y = 8
      have h_not_prime : ¬ Nat.Prime 116227 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 71)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 116227 ∧ 116227 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 116227 ∧ 116227 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 9
      rfl
    · -- y = 10
      have h_not_prime : ¬ Nat.Prime 107779 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 7)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 107779 ∧ 107779 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 107779 ∧ 107779 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 11
      rfl
    · -- y = 12
      have h_not_prime : ¬ Nat.Prime 73987 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 241)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 73987 ∧ 73987 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 73987 ∧ 73987 % 6 = 1 then 1 else 0) = 0
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
  · -- x = 9
    interval_cases y
    · -- y = 1
      rfl
    · -- y = 2
      have h_not_prime : ¬ Nat.Prime 118615 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 118615 ∧ 118615 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 118615 ∧ 118615 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 3
      rfl
    · -- y = 4
      have h_not_prime : ¬ Nat.Prime 118483 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 109)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 118483 ∧ 118483 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 118483 ∧ 118483 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 5
      rfl
    · -- y = 6
      have h_not_prime : ¬ Nat.Prime 117955 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 117955 ∧ 117955 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 117955 ∧ 117955 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 7
      rfl
    · -- y = 8
      have h_not_prime : ¬ Nat.Prime 115843 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 7)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 115843 ∧ 115843 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 115843 ∧ 115843 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 9
      rfl
    · -- y = 10
      have h_not_prime : ¬ Nat.Prime 107395 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 107395 ∧ 107395 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 107395 ∧ 107395 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 11
      rfl
    · -- y = 12
      have h_not_prime : ¬ Nat.Prime 73603 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 89)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 73603 ∧ 73603 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 73603 ∧ 73603 % 6 = 1 then 1 else 0) = 0
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
  · -- x = 11
    interval_cases y
    · -- y = 1
      rfl
    · -- y = 2
      have h_not_prime : ¬ Nat.Prime 117079 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 17)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 117079 ∧ 117079 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 117079 ∧ 117079 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 3
      rfl
    · -- y = 4
      have h_not_prime : ¬ Nat.Prime 116947 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 83)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 116947 ∧ 116947 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 116947 ∧ 116947 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 5
      rfl
    · -- y = 6
      have h_not_prime : ¬ Nat.Prime 116419 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 47)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 116419 ∧ 116419 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 116419 ∧ 116419 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 7
      rfl
    · -- y = 8
      have h_not_prime : ¬ Nat.Prime 114307 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 151)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 114307 ∧ 114307 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 114307 ∧ 114307 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 9
      rfl
    · -- y = 10
      have h_not_prime : ¬ Nat.Prime 105859 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 13)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 105859 ∧ 105859 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 105859 ∧ 105859 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 11
      rfl
    · -- y = 12
      have h_not_prime : ¬ Nat.Prime 72067 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 19)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 72067 ∧ 72067 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 72067 ∧ 72067 % 6 = 1 then 1 else 0) = 0
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
  · -- x = 12
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
  · -- x = 13
    interval_cases y
    · -- y = 1
      rfl
    · -- y = 2
      have h_not_prime : ¬ Nat.Prime 110935 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 110935 ∧ 110935 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 110935 ∧ 110935 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 3
      rfl
    · -- y = 4
      have h_not_prime : ¬ Nat.Prime 110803 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 7)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 110803 ∧ 110803 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 110803 ∧ 110803 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 5
      rfl
    · -- y = 6
      have h_not_prime : ¬ Nat.Prime 110275 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 110275 ∧ 110275 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 110275 ∧ 110275 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 7
      rfl
    · -- y = 8
      have h_not_prime : ¬ Nat.Prime 108163 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 11)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 108163 ∧ 108163 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 108163 ∧ 108163 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 9
      rfl
    · -- y = 10
      have h_not_prime : ¬ Nat.Prime 99715 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 5)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 99715 ∧ 99715 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 99715 ∧ 99715 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 11
      rfl
    · -- y = 12
      have h_not_prime : ¬ Nat.Prime 65923 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 11)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 65923 ∧ 65923 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 65923 ∧ 65923 % 6 = 1 then 1 else 0) = 0
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
  · -- x = 14
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
  · -- x = 15
    interval_cases y
    · -- y = 1
      rfl
    · -- y = 2
      have h_not_prime : ¬ Nat.Prime 86359 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 7)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 86359 ∧ 86359 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 86359 ∧ 86359 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 3
      rfl
    · -- y = 4
      have h_not_prime : ¬ Nat.Prime 86227 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 23)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 86227 ∧ 86227 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 86227 ∧ 86227 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 5
      rfl
    · -- y = 6
      have h_not_prime : ¬ Nat.Prime 85699 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 43)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 85699 ∧ 85699 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 85699 ∧ 85699 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 7
      rfl
    · -- y = 8
      have h_not_prime : ¬ Nat.Prime 83587 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 7)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 83587 ∧ 83587 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 83587 ∧ 83587 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 9
      rfl
    · -- y = 10
      have h_not_prime : ¬ Nat.Prime 75139 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 29)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 75139 ∧ 75139 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 75139 ∧ 75139 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 11
      rfl
    · -- y = 12
      have h_not_prime : ¬ Nat.Prime 41347 := by
        apply Nat.not_prime_of_dvd_of_lt (m := 173)
        · decide
        · decide
        · decide
      have h_and : ¬ (Nat.Prime 41347 ∧ 41347 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 41347 ∧ 41347 % 6 = 1 then 1 else 0) = 0
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
  · -- x = 16
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
  · -- x = 17
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
