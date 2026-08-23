import FormalConjectures.Util.ProblemImports

/-!
Development file: discrete circle method for the 2-4-6-8 problem.
Not the submission file. Experiment here, then port to Spec.lean.
-/

open Complex Real BigOperators Nat

noncomputable section

/-- `e(θ) = exp(2πi θ)`. -/
def e (θ : ℝ) : ℂ := cexp (2 * π * I * θ)

lemma e_add (a b : ℝ) : e (a + b) = e a * e b := by
  unfold e
  rw [← Complex.exp_add]
  ring_nf

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_int (n : ℤ) : e (n : ℝ) = 1 := by
  unfold e
  have : (2 * π * I * (n : ℂ)) = n * (2 * π * I) := by
    simp [mul_comm, mul_left_comm, mul_assoc]
    ring
  rw [this]
  simpa using Complex.exp_int_mul_two_pi_mul_I n

lemma e_nat (n : ℕ) : e (n : ℝ) = 1 := e_int n

lemma e_periodic (θ : ℝ) (n : ℤ) : e (θ + n) = e θ := by
  rw [e_add, e_int, mul_one]

lemma norm_e (θ : ℝ) : ‖e θ‖ = 1 := by
  simp [e, Complex.norm_exp]
  ring

lemma e_neg (θ : ℝ) : e (-θ) = starRingEnd ℂ (e θ) := by
  unfold e
  rw [← Complex.exp_conj]
  simp [map_mul, map_ofNat]
  ring_nf
  simp [starRingEnd]

/-- Geometric sum bound: `|∑_{j=0}^{N-1} e(jα)| ≤ min(N, 1 / |sin(πα)|)`. -/
lemma norm_geom_sum_le (α : ℝ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, e (j * α)‖ ≤ N := by
  refine (norm_sum_le _ _).trans ?_
  simp [norm_e]

/-- Exact orthogonality: `(1/Q) ∑_{h=0}^{Q-1} e(h * m / Q) = 1` iff `Q ∣ m`. -/
lemma sum_e_div_eq (Q : ℕ) (hQ : 0 < Q) (m : ℤ) :
    ∑ h ∈ Finset.range Q, e (h * m / Q) =
      if Q ∣ m then (Q : ℂ) else 0 := by
  sorry

end
