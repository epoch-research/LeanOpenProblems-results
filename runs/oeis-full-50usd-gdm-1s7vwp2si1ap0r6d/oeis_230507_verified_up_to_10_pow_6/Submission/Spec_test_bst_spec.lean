import FormalConjectures.Util.ProblemImports

def S_condition (m : ℕ) : Prop := m = 1 ∨ m = 2 ∨ m = 5

theorem S_condition_C_1 : S_condition 1 := by simp [S_condition]
theorem S_condition_C_2 : S_condition 2 := by simp [S_condition]
theorem S_condition_C_5 : S_condition 5 := by simp [S_condition]

def CustomS (m : ℕ) : Bool :=
  if m ≤ 2 then
    if m ≤ 1 then m == 1 else m == 2
  else
    m == 5

theorem CustomS_spec (m : ℕ) (h : CustomS m = true) : S_condition m := by
  dsimp [CustomS] at h
  by_cases h1 : m ≤ 2
  · simp [h1] at h
    by_cases h2 : m ≤ 1
    · simp [h2] at h
      have : m = 1 := by omega
      subst this
      exact S_condition_C_1
    · simp [h2] at h
      have : m = 2 := by omega
      subst this
      exact S_condition_C_2
  · simp [h1] at h
    have : m = 5 := by omega
    subst this
    exact S_condition_C_5
