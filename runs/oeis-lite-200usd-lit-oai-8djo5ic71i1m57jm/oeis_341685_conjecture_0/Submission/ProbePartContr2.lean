import FormalConjectures.Util.ProblemImports

example : Part.some (0 : ℕ) = (⊥ : Part ℕ) := by
  exact Part.get_eq_get (a := Part.some (0:ℕ)) (b := (⊥ : Part ℕ)) (by simp) (by simp)

example : False := by
  have h : Part.some (0 : ℕ) = (⊥ : Part ℕ) := by
    exact Part.get_eq_get (a := Part.some (0:ℕ)) (b := (⊥ : Part ℕ)) (by simp) (by simp)
  have hs : (Part.some (0:ℕ)).Dom := by simp
  rw [h] at hs
  simpa using hs

theorem partFalse : False := by
  have h : Part.some (0 : ℕ) = (⊥ : Part ℕ) := by
    exact Part.get_eq_get (a := Part.some (0:ℕ)) (b := (⊥ : Part ℕ)) (by simp) (by simp)
  have hs : (Part.some (0:ℕ)).Dom := by simp
  rw [h] at hs
  simpa using hs

#print axioms partFalse
