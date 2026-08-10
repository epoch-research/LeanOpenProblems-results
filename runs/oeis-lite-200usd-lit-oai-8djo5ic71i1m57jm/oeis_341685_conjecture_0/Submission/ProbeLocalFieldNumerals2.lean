import FormalConjectures.Util.ProblemImports

example : True := by
  letI : Field ℤ := Classical.choice (Infinite.nonempty_field (α := ℤ))
  have h0 : (0 : ℤ) = Int.ofNat 0 := by rfl
  have h1 : (1 : ℤ) = Int.ofNat 1 := by rfl
  have hfield : (0 : ℤ) ≠ (1 : ℤ) := zero_ne_one
  have hstdne : (0 : ℤ) ≠ (1 : ℤ) := by norm_num
  trivial

#check (zero_ne_one : (0 : ℤ) ≠ (1 : ℤ))
