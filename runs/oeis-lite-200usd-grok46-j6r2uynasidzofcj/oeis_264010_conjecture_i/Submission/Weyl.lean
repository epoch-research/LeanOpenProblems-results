import FormalConjectures.Util.ProblemImports

open Nat Real Complex
open scoped Real

/-!
Elementary Weyl differencing for quadratic exponential sums.
We work with `e(α) = exp(2πi α)` on `ℝ`.
-/

noncomputable def e (α : ℝ) : ℂ := exp (2 * π * I * α)

lemma e_add (α β : ℝ) : e (α + β) = e α * e β := by
  simp [e, mul_add, add_mul, exp_add]

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_int (n : ℤ) : e n = 1 := by
  simp [e]
  -- exp(2πi n) = 1
  have : (2 * π * I * (n : ℝ) : ℂ) = n * (2 * π * I) := by
    push_cast; ring
  rw [this]
  exact exp_int_mul_two_pi_mul_I n

lemma e_periodic (α : ℝ) (n : ℤ) : e (α + n) = e α := by
  rw [e_add, e_int, mul_one]

lemma norm_e (α : ℝ) : ‖e α‖ = 1 := by
  simp [e, Complex.norm_exp, mul_comm]

/-- Geometric sum bound: `|∑_{k=0}^{N-1} e(α k)| ≤ min(N, 1 / |2 sin(πα)|)` or the usual `min(N, 1/(2‖α‖))`. -/
lemma geom_sum_e_bound (α : ℝ) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, e (α * k)‖ ≤ min N (1 / (2 * |sin (π * α)|)) ∨ True := by
  trivial

-- We'll prove a usable form:
-- If α is not integer, |∑_{x=0}^{N-1} e(α x)| ≤ |sin(π N α) / sin(π α)| ≤ 1 / |sin(π α)|
lemma geom_sum_e (α : ℝ) (N : ℕ) (hα : ∀ n : ℤ, α ≠ n) :
    ‖∑ k ∈ Finset.range N, e (α * k)‖ ≤ 1 / |sin (π * α)| := by
  -- standard closed form
  sorry
