import FormalConjectures.Util.ProblemImports
example (A n : ℕ) (hdiv : (16 * 3^n) ∣ A) :
    (A : ℚ) / (3^n : ℚ) = (16 * (A / (16 * 3^n)) : ℕ) := by
  have hmul : (16 * 3^n) * (A / (16 * 3^n)) = A := Nat.mul_div_cancel' hdiv
  rw [← hmul]
  norm_num
  field_simp [pow_ne_zero n (by norm_num : (3:ℚ) ≠ 0)]
