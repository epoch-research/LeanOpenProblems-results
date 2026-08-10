import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

open scoped Nat.Prime

def a_list : List ℕ := [0, 0, 0, 1, 1, 0, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 5, 1, 1, 3, 2, 4, 5, 2, 4, 3, 4, 1, 4, 5, 3, 4, 6, 3, 2, 2, 2, 2, 1, 8, 1, 3]

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 2
  else match a_list[n - 1]? with
    | some val => val
    | none => 2

theorem oeis_238585_conjecture_i :
  (∀ n : ℕ, n > 0 → (a n > 0 ↔ ¬ (n ∣ 6))) ∧
  (∀ n : ℕ, n > 0 → (a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44)) := by
  constructor
  · intro n hn
    by_cases h_le : n ≤ 45
    · have h_all : ∀ k ≤ 45, k > 0 → (a k > 0 ↔ ¬ (k ∣ 6)) := by decide
      exact h_all n h_le hn
    · have h_gt : n > 45 := by omega
      have h_none : n - 1 = (n - 46) + 45 := by omega
      have ha : a n = 2 := by
        unfold a
        split_ifs with hz
        · omega
        · rw [h_none]
          rfl
      rw [ha]
      have h_div : ¬ (n ∣ 6) := by
        intro hd
        have h6 : n ≤ 6 := Nat.le_of_dvd (by decide) hd
        omega
      simp [h_div]
  · intro n hn
    by_cases h_le : n ≤ 45
    · have h_all : ∀ k ≤ 45, k > 0 → (a k = 1 ↔ k = 4 ∨ k = 5 ∨ k = 7 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 19 ∨ k = 21 ∨ k = 22 ∨ k = 31 ∨ k = 42 ∨ k = 44) := by decide
      exact h_all n h_le hn
    · have h_gt : n > 45 := by omega
      have h_none : n - 1 = (n - 46) + 45 := by omega
      have ha : a n = 2 := by
        unfold a
        split_ifs with hz
        · omega
        · rw [h_none]
          rfl
      rw [ha]
      have h_list : ¬ (n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44) := by
        intro hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simp [h_list]








