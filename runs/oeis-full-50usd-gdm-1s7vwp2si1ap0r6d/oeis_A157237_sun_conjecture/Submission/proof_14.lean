import FormalConjectures.Util.ProblemImports
open Nat

theorem a_eq_zero_14 : a 14 = 0 := by
  dsimp [a]
  apply Finset.sum_eq_zero
  intro pair h_mem
  rcases pair with ⟨x, y⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem
  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  change x ≤ 5 at hx2
  change y ≤ 5 at hy2
  interval_cases x
  · -- x = 1
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
  · -- x = 2
    interval_cases y
    · -- y = 1
      have h_not_prime : ¬ Nat.Prime 1 := Nat.not_prime_one
      have h_and : ¬ (Nat.Prime 1 ∧ 1 % 6 = 1) := fun h => h_not_prime h.1
      change (if Nat.Prime 1 ∧ 1 % 6 = 1 then 1 else 0) = 0
      rw [if_neg h_and]
    · -- y = 2
      rfl
    · -- y = 3
      rfl
    · -- y = 4
      rfl
    · -- y = 5
      rfl
  · -- x = 3
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
  · -- x = 5
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
