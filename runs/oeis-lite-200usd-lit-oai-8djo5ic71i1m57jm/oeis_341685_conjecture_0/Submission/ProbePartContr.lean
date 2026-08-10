import FormalConjectures.Util.ProblemImports

#check Part.get_eq_get
#check Part.assert
#check Part.some
#check Part.none
#check Part.get
#check Part.mem_iff

example : False := by
  -- Try prove Part.some 0 = Part.none then domain contradiction
  have h : Part.some (0 : ℕ) = (⊥ : Part ℕ) := by
    fail_if_success exact Part.get_eq_get (a := Part.some (0:ℕ)) (b := (⊥ : Part ℕ)) (by simp) (by simp)
    sorry
  have hs : (Part.some (0:ℕ)).Dom := by simp
  rw [h] at hs
  simpa using hs
