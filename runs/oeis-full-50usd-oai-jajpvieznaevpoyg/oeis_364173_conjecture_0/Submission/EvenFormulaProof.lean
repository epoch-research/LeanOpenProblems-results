import FormalConjectures.Util.ProblemImports

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

example (k : ℕ) :
    a (2 * k) =
      ((Nat.factorial (18*k) : ℝ) * (Nat.factorial (4*k) : ℝ) * (Nat.factorial (3*k) : ℝ)) /
      ((Nat.factorial (9*k) : ℝ) * (Nat.factorial (8*k) : ℝ) * (Nat.factorial (6*k) : ℝ) * (Nat.factorial (2*k) : ℝ)) := by
  unfold a
  ring_nf
  rw [(by convert Real.Gamma_nat_eq_factorial (18*k) using 1 <;> (congr 1; norm_num [Nat.cast_mul]; ring_nf) : Real.Gamma (1 + ↑(k*2) * 9) = ((18*k).factorial : ℝ))]
  rw [(by convert Real.Gamma_nat_eq_factorial (4*k) using 1 <;> (congr 1; norm_num [Nat.cast_mul]; ring_nf) : Real.Gamma (1 + ↑(k*2) * 2) = ((4*k).factorial : ℝ))]
  rw [(by convert Real.Gamma_nat_eq_factorial (3*k) using 1 <;> (congr 1; norm_num [Nat.cast_mul]; ring_nf) : Real.Gamma (1 + ↑(k*2) * (3/2 : ℝ)) = ((3*k).factorial : ℝ))]
  rw [(by convert Real.Gamma_nat_eq_factorial (9*k) using 1 <;> (congr 1; norm_num [Nat.cast_mul]; ring_nf) : Real.Gamma (1 + ↑(k*2) * (9/2 : ℝ)) = ((9*k).factorial : ℝ))]
  rw [(by convert Real.Gamma_nat_eq_factorial (8*k) using 1 <;> (congr 1; norm_num [Nat.cast_mul]; ring_nf) : Real.Gamma (1 + ↑(k*2) * 4) = ((8*k).factorial : ℝ))]
  rw [(by convert Real.Gamma_nat_eq_factorial (6*k) using 1 <;> (congr 1; norm_num [Nat.cast_mul]; ring_nf) : Real.Gamma (1 + ↑(k*2) * 3) = ((6*k).factorial : ℝ))]
  rw [(by convert Real.Gamma_nat_eq_factorial (2*k) using 1 <;> (congr 1; norm_num [Nat.cast_mul]; ring_nf) : Real.Gamma (1 + ↑(k*2)) = ((2*k).factorial : ℝ))]
  ring
