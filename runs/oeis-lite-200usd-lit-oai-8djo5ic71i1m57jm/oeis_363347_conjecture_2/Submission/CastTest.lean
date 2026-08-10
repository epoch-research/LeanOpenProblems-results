import FormalConjectures.Util.ProblemImports
example (r:ℕ) (hr:4≤r): ((r-2:ℕ):ℚ) = (r:ℚ)-2 := by
  rw [Nat.cast_sub (by omega : 2 ≤ r)]
  norm_num
example (r:ℕ) (hr:4≤r): ((r-1:ℕ):ℚ) = (r:ℚ)-1 := by
  rw [Nat.cast_sub (by omega : 1 ≤ r)]
  norm_num
