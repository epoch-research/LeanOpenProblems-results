import Submission.Reduction

/-!
# The analytic consequence of a quadratic bound for Erdős problem 126

The arithmetic inequality is an explicit hypothesis.  Since `log n ^ 2 = o(n)`,
it implies the uniform lower bound from `Submission.Reduction`, and hence the
required limit for every function satisfying the original extremal specification.
-/

open Filter
open scoped Topology

namespace Erdos126Limit

open Erdos126Reduction

/-- The quadratic cardinality bound implies the uniform logarithmic lower bound.
Squaring the real constant treats positive and negative constants uniformly. -/
theorem uniformBound_of_quadratic
    (h : ∀ A : Finset ℕ, A.card ≤ 3 * (P A) ^ 2 + 2) : UniformBound := by
  intro C
  have hlim : Tendsto
      (fun n : ℕ => 3 * (C * Real.log (n : ℝ)) ^ 2 / ((n : ℝ) - 2))
      atTop (𝓝 0) := by
    have hlog :=
      ((Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 2 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).const_mul
          (3 * C ^ 2)
    simpa only [Function.comp_def, one_mul, sub_eq_add_neg, mul_zero, mul_pow,
      mul_assoc, mul_div_assoc] using hlog
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const zero_lt_one)
  refine ⟨max N 3, ?_⟩
  intro A hA
  have hlarge : 3 ≤ A.card := (le_max_right N 3).trans hA
  have hdenom : 0 < (A.card : ℝ) - 2 := by
    have hthree : (3 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hlarge
    linarith
  have hsmall : 3 * (C * Real.log (A.card : ℝ)) ^ 2 < (A.card : ℝ) - 2 := by
    have hx := (div_lt_iff₀ hdenom).mp (hN A.card ((le_max_left N 3).trans hA))
    simpa only [one_mul] using hx
  have hquad : (A.card : ℝ) ≤ 3 * (P A : ℝ) ^ 2 + 2 := by
    exact_mod_cast h A
  apply le_of_sq_le_sq _ (Nat.cast_nonneg (P A))
  nlinarith only [hquad, hsmall]

/-- Apply the existing extremal-function reduction to the quadratic bound. -/
theorem tendsto_of_quadratic {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f)
    (h : ∀ A : Finset ℕ, A.card ≤ 3 * (P A) ^ 2 + 2) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop :=
  tendsto_of_uniformBound hf (uniformBound_of_quadratic h)

/-- The quadratic bound suffices for the universally quantified conjecture. -/
theorem conjecture_of_quadratic
    (h : ∀ A : Finset ℕ, A.card ≤ 3 * (P A) ^ 2 + 2) : Conjecture := by
  intro f hf
  exact tendsto_of_quadratic hf h

end Erdos126Limit
