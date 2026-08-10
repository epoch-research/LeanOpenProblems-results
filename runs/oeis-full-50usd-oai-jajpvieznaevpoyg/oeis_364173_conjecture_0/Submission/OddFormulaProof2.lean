import FormalConjectures.Util.ProblemImports

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

example (k : ℕ) :
    a (2 * k + 1) =
      ((4 : ℝ) ^ (6*k + 3) * (Nat.factorial (4*k+2) : ℝ) * (Nat.factorial (9*k+4) : ℝ)) /
      ((Nat.factorial (3*k+1) : ℝ) * (Nat.factorial (8*k+4) : ℝ) * (Nat.factorial (2*k+1) : ℝ)) := by
  unfold a
  ring_nf
  rw [(by convert Real.Gamma_nat_eq_factorial (18*k+9) using 1 <;> (congr 1; norm_num [Nat.cast_mul, Nat.cast_add]; ring_nf) :
    Real.Gamma (1 + ↑(1 + k * 2) * 9) = ((18*k+9).factorial : ℝ))]
  rw [(by convert Real.Gamma_nat_eq_factorial (4*k+2) using 1 <;> (congr 1; norm_num [Nat.cast_mul, Nat.cast_add]; ring_nf) :
    Real.Gamma (1 + ↑(1 + k * 2) * 2) = ((4*k+2).factorial : ℝ))]
  rw [(by convert Real.Gamma_nat_add_half (3*k+2) using 1 <;> (congr 1; norm_num [Nat.cast_mul, Nat.cast_add]; ring_nf) :
    Real.Gamma (1 + ↑(1 + k * 2) * (3 / 2 : ℝ)) = ((2*(3*k+2)-1).doubleFactorial : ℝ) * √Real.pi / 2^(3*k+2))]
  rw [(by convert Real.Gamma_nat_add_half (9*k+5) using 1 <;> (congr 1; norm_num [Nat.cast_mul, Nat.cast_add]; ring_nf) :
    Real.Gamma (1 + ↑(1 + k * 2) * (9 / 2 : ℝ)) = ((2*(9*k+5)-1).doubleFactorial : ℝ) * √Real.pi / 2^(9*k+5))]
  rw [(by convert Real.Gamma_nat_eq_factorial (8*k+4) using 1 <;> (congr 1; norm_num [Nat.cast_mul, Nat.cast_add]; ring_nf) :
    Real.Gamma (1 + ↑(1 + k * 2) * 4) = ((8*k+4).factorial : ℝ))]
  rw [(by convert Real.Gamma_nat_eq_factorial (6*k+3) using 1 <;> (congr 1; norm_num [Nat.cast_mul, Nat.cast_add]; ring_nf) :
    Real.Gamma (1 + ↑(1 + k * 2) * 3) = ((6*k+3).factorial : ℝ))]
  rw [(by convert Real.Gamma_nat_eq_factorial (2*k+1) using 1 <;> (congr 1; norm_num [Nat.cast_mul, Nat.cast_add]; ring_nf) :
    Real.Gamma (1 + ↑(1 + k * 2)) = ((2*k+1).factorial : ℝ))]
  -- Now only double factorial/factorial algebra remains.
  have hdf1 : (2 * (3*k+2) - 1) = 6*k+3 := by omega
  have hdf2 : (2 * (9*k+5) - 1) = 18*k+9 := by omega
  rw [hdf1, hdf2]
  rw [show (18*k+9).factorial = (18*k+9).doubleFactorial * (18*k+8).doubleFactorial by
    convert Nat.factorial_eq_mul_doubleFactorial (18*k+8) using 1 <;> omega]
  rw [show (6*k+3).factorial = (6*k+3).doubleFactorial * (6*k+2).doubleFactorial by
    convert Nat.factorial_eq_mul_doubleFactorial (6*k+2) using 1 <;> omega]
  have h18 : 18*k+8 = 2*(9*k+4) := by omega
  rw [h18, Nat.doubleFactorial_two_mul]
  have h6 : 6*k+2 = 2*(3*k+1) := by omega
  rw [h6, Nat.doubleFactorial_two_mul]
  field_simp [(Real.sqrt_ne_zero Real.pi_pos.le).2 Real.pi_pos.ne']
  norm_num [Nat.cast_mul, Nat.cast_pow] at *
  rw [show (4 : ℝ) ^ (k * 6) = (2 : ℝ) ^ (k * 12) by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    rw [← pow_mul]
    congr 1
    omega]
  ring_nf
