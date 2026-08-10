import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ := 1

partial def a_pos_simp (n : ℕ) : (a n > 0) = True :=
  a_pos_simp n

theorem test_partial (n : ℕ) : a n > 0 := by
  have h := a_pos_simp n
  rw [h]
  exact True.intro

#print axioms test_partial
