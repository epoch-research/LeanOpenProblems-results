import FormalConjectures.Util.ProblemImports
#check Int.mul_ediv_cancel_left
#check Int.ediv_mul_cancel
example (a z : ℤ) : (16 * a - 16 * z) / 8 = 2 * (a - z) := by
  rw [show 16 * a - 16 * z = 8 * (2 * (a - z)) by ring]
  rw [Int.mul_ediv_cancel_left]
  norm_num
