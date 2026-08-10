import FormalConjectures.Util.ProblemImports
open Nat

theorem a_eq_zero_12 : a 12 = 0 := by
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
      rfl
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
