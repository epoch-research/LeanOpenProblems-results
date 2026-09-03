import Submission.KernelPowerObstruction

/-!
Distinct rational bivariate polynomials differ at all sufficiently late
factorial nodes. The application to powers of telescoping kernels is only an
auxiliary obstruction and does not settle Erdős 68.
-/

namespace FactorialNodePolynomials

open Polynomial Filter KernelPowerObstruction KernelNonvanishing RationalKernelForms
open scoped Topology

noncomputable section

/-- Evaluation at the original row `n+2` and its reciprocal factorial. -/
def nodeEval (P : Bivariate) (n : ℕ) : ℝ :=
  P.eval₂ ((Rat.castHom ℝ).comp (evalRingHom ((n + 2 : ℕ) : ℚ)))
    (1 / ((n + 2).factorial : ℝ))

lemma tendsto_polynomial_recip (P : Polynomial ℚ) (j : ℕ) :
    Tendsto (fun n : ℕ => ((P.eval ((n + 2 : ℕ) : ℚ) : ℚ) : ℝ) *
      (1 / ((n + 2).factorial : ℝ)) ^ (j + 1)) atTop (𝓝 0) := by
  have hs := summable_eval_div_factorial_pow P (j + 1) (by omega)
  have ht := ((summable_nat_add_iff 2).mpr hs).tendsto_atTop_zero
  simpa only [div_pow, one_pow, mul_one_div] using ht

lemma tendsto_remainder (P : Bivariate) :
    Tendsto (fun n : ℕ => nodeEval P n -
      (((P.coeff 0).eval ((n + 2 : ℕ) : ℚ) : ℚ) : ℝ)) atTop (𝓝 0) := by
  have ht := tendsto_finset_sum (Finset.range P.natDegree) (fun j _ =>
    tendsto_polynomial_recip (P.coeff (j + 1)) j)
  convert ht using 1
  · funext n
    simp only [nodeEval, eval₂_eq_sum_range, Finset.sum_range_succ',
      RingHom.coe_comp, Function.comp_apply, coe_evalRingHom,
      Rat.coe_castHom, pow_zero, mul_one]
    ring
  · simp

lemma eval_cast_polynomial (P : Polynomial ℚ) (n : ℕ) :
    (P.map (Rat.castHom ℝ)).eval ((n + 2 : ℕ) : ℝ) =
      ((P.eval ((n + 2 : ℕ) : ℚ) : ℚ) : ℝ) := by
  simpa only [Rat.cast_natCast] using
    (eval_map_apply (f := Rat.castHom ℝ) (p := P) ((n + 2 : ℕ) : ℚ))

lemma eventually_node_ne_zero_of_constant (P : Bivariate) (hP : P.coeff 0 ≠ 0) :
    ∀ᶠ n : ℕ in atTop, nodeEval P n ≠ 0 := by
  have hmap : (P.coeff 0).map (Rat.castHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Rat.castHom ℝ).injective).mpr hP
  obtain ⟨c, hc, hb⟩ := polynomial_abs_eventually_ge _ hmap
  have hr := (tendsto_order.mp (tendsto_remainder P).abs).2 c (by simpa using hc)
  filter_upwards [hb, hr] with n hn he
  intro hz
  rw [eval_cast_polynomial] at hn
  rw [hz, zero_sub, abs_neg] at he
  exact (not_lt_of_ge hn) he

/-- Factorial decay separates the lowest nonzero outer coefficient from all
higher powers, regardless of the inner polynomial degrees. -/
theorem eventually_node_ne_zero (P : Bivariate) (hP : P ≠ 0) :
    ∀ᶠ n : ℕ in atTop, nodeEval P n ≠ 0 := by
  have main : ∀ d : ℕ, ∀ Q : Bivariate, Q.natDegree = d → Q ≠ 0 →
      ∀ᶠ n : ℕ in atTop, nodeEval Q n ≠ 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro Q hd hQ
      by_cases hc : Q.coeff 0 = 0
      · have he : X * Q.divX = Q := by simpa [hc] using X_mul_divX_add Q
        have hdiv : Q.divX ≠ 0 := by
          intro hz
          apply hQ
          rw [← he, hz, mul_zero]
        have hdeg : Q.divX.natDegree < d := by
          have hh := natDegree_X_mul hdiv
          rw [he, hd] at hh
          omega
        have ht := ih _ hdeg Q.divX rfl hdiv
        filter_upwards [ht] with n hn
        rw [← he]
        simpa only [nodeEval, eval₂_mul, eval₂_X] using
          mul_ne_zero (by positivity : (1 / ((n + 2).factorial : ℝ)) ≠ 0) hn
      · exact eventually_node_ne_zero_of_constant Q hc
  exact main P.natDegree P rfl hP

/-- Agreement at all sufficiently late factorial nodes implies formal equality. -/
theorem eq_of_eventually_node_eq (P Q : Bivariate)
    (h : ∀ᶠ n : ℕ in atTop, nodeEval P n = nodeEval Q n) : P = Q := by
  by_contra hpq
  have ht := eventually_node_ne_zero (P - Q) (sub_ne_zero.mpr hpq)
  obtain ⟨n, hn, he⟩ := (h.and ht).exists
  exact he (by simpa only [nodeEval, eval₂_sub, sub_eq_zero] using hn)

lemma nodeEval_formalKernel (A : ℚ) (H : ℕ → Polynomial ℚ) (J n : ℕ) :
    nodeEval (formalKernel A H J) n =
      kernel A H J n (1 / ((n + 2).factorial : ℝ)) := by
  simp only [nodeEval, formalKernel, columnSum, kernel, eval₂_sub, eval₂_mul,
    eval₂_C, eval₂_one, eval₂_X, eval₂_finset_sum, eval₂_pow,
    RingHom.comp_apply, coe_evalRingHom, Rat.coe_castHom, eval_C,
    PositiveKernelBoundary.columnOperator_eval_row]

lemma nodeEval_basicKernel (A : ℚ) (n : ℕ) :
    nodeEval (basicKernel A) n = (A : ℝ) -
      (1 - 1 / ((n + 2).factorial : ℝ)) * (n + 1) := by
  simp only [nodeEval, basicKernel, eval₂_sub, eval₂_mul, eval₂_C, eval₂_one,
    eval₂_X, RingHom.comp_apply, coe_evalRingHom, Rat.coe_castHom,
    eval_C, eval_sub, eval_X, eval_one, Rat.cast_sub, Rat.cast_natCast, Rat.cast_one]
  push_cast
  ring

/-- The obstruction persists even if equality is required only at factorial
nodes, rather than as a formal bivariate polynomial identity. -/
theorem eventually_power_ne_kernel (A B : ℚ) (j : ℕ) (hj : 1 ≤ j)
    (H : ℕ → Polynomial ℚ) (J : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((A : ℝ) - (1 - 1 / ((n + 2).factorial : ℝ)) * (n + 1)) ^ (j + 1) ≠
        kernel B H J n (1 / ((n + 2).factorial : ℝ)) := by
  have hp := basic_power_not_kernel A B j hj H J
  have ht := eventually_node_ne_zero
    ((basicKernel A) ^ (j + 1) - formalKernel B H J) (sub_ne_zero.mpr hp)
  filter_upwards [ht] with n hn
  have he : nodeEval ((basicKernel A) ^ (j + 1) - formalKernel B H J) n =
      (nodeEval (basicKernel A) n) ^ (j + 1) - nodeEval (formalKernel B H J) n := by
    simp [nodeEval, eval₂_pow]
  rw [he, nodeEval_basicKernel, nodeEval_formalKernel, sub_ne_zero] at hn
  exact hn

end

end FactorialNodePolynomials

#print axioms FactorialNodePolynomials.eventually_node_ne_zero
#print axioms FactorialNodePolynomials.eq_of_eventually_node_eq
#print axioms FactorialNodePolynomials.eventually_power_ne_kernel
