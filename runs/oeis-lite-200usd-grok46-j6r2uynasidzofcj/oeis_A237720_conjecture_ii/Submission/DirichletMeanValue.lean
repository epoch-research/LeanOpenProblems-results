import FormalConjectures.Util.ProblemImports

/-!
Mean-value theorem for Dirichlet polynomials.

  ∫_{0}^{T} |∑_{n=1}^{N} a n ^{it}|^2 dt  ≤  (T + O(N)) ∑ |a n|^2

This is the basic L² estimate used in Ingham-type zero-density arguments.
-/

open Complex Real MeasureTheory
open scoped BigOperators

noncomputable section

/-- `n^{it} = exp(i t log n)` for a positive integer `n`. -/
lemma nat_cpow_I_mul {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (n : ℂ) ^ (I * t) = Complex.exp (I * t * Real.log n) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [cpow_def_of_ne_zero hn0]
  simp [log_natCast hn.ne', mul_comm]

/-- The standard Montgomery–Vaughan / Gallagher mean value:
the off-diagonal terms are bounded by `∑_{n,m} |aₙ aₘ| / |log(n/m)|`. -/
lemma dirichlet_mean_offdiag {N : ℕ} (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hnm : n ≠ m) :
    ‖∫ t in (0 : ℝ)..T, ((n : ℂ) ^ (I * t)) * ((m : ℂ) ^ (-I * t))‖
      ≤ 2 / |Real.log n - Real.log m| := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlog : Real.log n ≠ Real.log m := by
    intro h
    have : (n : ℝ) = m := (log_injOn_pos (Set.mem_Ioi.mpr hn0) (Set.mem_Ioi.mpr hm0) h)
    exact hnm (Nat.cast_injective this)
  -- n^{it} m^{-it} = exp(i t (log n - log m))
  have hfun :
      (fun t : ℝ ↦ ((n : ℂ) ^ (I * (t : ℂ))) * ((m : ℂ) ^ (-I * (t : ℂ))))
        = fun t : ℝ ↦ Complex.exp (I * t * (Real.log n - Real.log m)) := by
    ext t
    rw [nat_cpow_I_mul hn t, nat_cpow_I_mul hm t]
    -- m^{-it} = exp(-i t log m)
    have : (m : ℂ) ^ (-I * (t : ℂ)) = Complex.exp (-I * t * Real.log m) := by
      have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
      rw [cpow_def_of_ne_zero hmC]
      simp [log_natCast hm.ne']
    rw [this, ← Complex.exp_add]
    ring_nf
  -- This is a placeholder bound; the integral of e^{iλt} has norm ≤ 2/|λ|.
  sorry

end
