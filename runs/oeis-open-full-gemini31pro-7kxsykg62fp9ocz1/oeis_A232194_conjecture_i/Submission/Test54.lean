import FormalConjectures.Util.ProblemImports

def P_test (a : ℕ → ℕ) (n : ℕ) : Prop := (n > 2 → a n > 0) ∧ (a n = 1 ↔ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 20 ∨ n = 24)
def P_parse1 (a : ℕ → ℕ) (n : ℕ) : Prop := ((n > 2 → a n > 0) ∧ a n = 1) ↔ (n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 20 ∨ n = 24)
def P_parse2 (a : ℕ → ℕ) (n : ℕ) : Prop := (n > 2 → a n > 0) ∧ ((a n = 1) ↔ (n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 20 ∨ n = 24))

theorem t1 : P_test = P_parse1 := by rfl
theorem t2 : P_test = P_parse2 := by rfl
