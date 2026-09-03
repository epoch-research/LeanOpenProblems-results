import Submission.FiniteKernelInterpolation

/-!
# Rational polynomial kernels with only boundary integrality

Auxiliary work for Erdős 68. No family of small nonzero integer forms is
constructed, and the conjecture is not settled here.
-/

namespace RationalKernelForms

lemma summable_eval_div_factorial_pow (H : Polynomial ℚ) (j : ℕ) (hj : 1 ≤ j) :
    Summable (fun n : ℕ =>
      ((H.eval (n : ℚ) : ℚ) : ℝ) / (n.factorial : ℝ) ^ j) := by
  apply (FiniteKernelInterpolation.summable_eval_div_factorial H).norm.of_norm_bounded
  intro n
  have hf : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hp : (n.factorial : ℝ) ≤ (n.factorial : ℝ) ^ j := by
    simpa using pow_le_pow_right₀ hf hj
  simp only [norm_div, Real.norm_eq_abs, abs_pow,
    abs_of_nonneg (show (0 : ℝ) ≤ n.factorial by positivity)]
  gcongr

noncomputable def rowCoeff (H : Polynomial ℚ) (j n : ℕ) : ℚ :=
  ((n + 2 : ℕ) : ℚ) ^ j * H.eval ((n + 1 : ℕ) : ℚ) -
    H.eval ((n + 2 : ℕ) : ℚ)

noncomputable def scaledEval (H : Polynomial ℚ) (j n : ℕ) : ℝ :=
  ((H.eval (n : ℚ) : ℚ) : ℝ) / (n.factorial : ℝ) ^ j

lemma summable_scaledEval (H : Polynomial ℚ) (j : ℕ) (hj : 1 ≤ j) :
    Summable (scaledEval H j) := summable_eval_div_factorial_pow H j hj

lemma rowCoeff_div (H : Polynomial ℚ) (j n : ℕ) :
    (rowCoeff H j n : ℝ) / ((n + 2).factorial : ℝ) ^ j =
      scaledEval H j (n + 1) - scaledEval H j (n + 2) := by
  have hf : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  have hn : (n + 2 : ℝ) ≠ 0 := by positivity
  have hfac : ((n + 2).factorial : ℝ) =
      (n + 2 : ℝ) * ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ (n + 1)
  unfold rowCoeff scaledEval
  push_cast
  rw [hfac, mul_pow]
  field_simp

lemma hasSum_rowCoeff (H : Polynomial ℚ) (j : ℕ) (hj : 1 ≤ j) :
    HasSum (fun n : ℕ => (rowCoeff H j n : ℝ) / ((n + 2).factorial : ℝ) ^ j)
      ((H.eval 1 : ℚ) : ℝ) := by
  have hs := summable_scaledEval H j hj
  have hs1 : Summable (fun n => scaledEval H j (n + 1)) :=
    (summable_nat_add_iff 1).mpr hs
  have hs2 : Summable (fun n => scaledEval H j (n + 2)) :=
    (summable_nat_add_iff 2).mpr hs
  have he := Summable.sum_add_tsum_nat_add 1 hs1
  have he' : (∑' n, scaledEval H j (n + 1)) -
      (∑' n, scaledEval H j (n + 2)) = ((H.eval 1 : ℚ) : ℝ) := by
    simp only [Finset.sum_range_one, zero_add, Nat.add_assoc] at he
    have hbase : scaledEval H j 1 = ((H.eval 1 : ℚ) : ℝ) := by
      simp [scaledEval]
    rw [hbase] at he
    linarith
  simpa only [rowCoeff_div, he'] using hs1.hasSum.sub hs2.hasSum

end RationalKernelForms

namespace RationalKernelForms

/-- The numerator of the weighted original row. -/
noncomputable def kernel (A : ℚ) (H : ℕ → Polynomial ℚ) (J n : ℕ) (t : ℝ) : ℝ :=
  (A : ℝ) - (1 - t) *
    ∑ j ∈ Finset.range J, (rowCoeff (H j) (j + 1) n : ℝ) * t ^ j

noncomputable def boundary (H : ℕ → Polynomial ℚ) (J : ℕ) : ℚ :=
  ∑ j ∈ Finset.range J, (H j).eval 1

lemma kernel_div (A : ℚ) (H : ℕ → Polynomial ℚ) (J n : ℕ) :
    kernel A H J n (1 / ((n + 2).factorial : ℝ)) /
        (((n + 2).factorial : ℝ) - 1) =
      (A : ℝ) / (((n + 2).factorial : ℝ) - 1) -
        ∑ j ∈ Finset.range J,
          (rowCoeff (H j) (j + 1) n : ℝ) / ((n + 2).factorial : ℝ) ^ (j + 1) := by
  have hf : ((n + 2).factorial : ℝ) ≠ 0 := by positivity
  have hd : ((n + 2).factorial : ℝ) - 1 ≠ 0 :=
    ne_of_gt (Erdos68Development.denom_pos n)
  unfold kernel
  rw [sub_div, Finset.mul_sum, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [div_pow, one_pow, pow_succ]
  field_simp

lemma hasSum_rows (H : ℕ → Polynomial ℚ) (J : ℕ) :
    HasSum (fun n : ℕ => ∑ j ∈ Finset.range J,
      (rowCoeff (H j) (j + 1) n : ℝ) / ((n + 2).factorial : ℝ) ^ (j + 1))
      ((boundary H J : ℚ) : ℝ) := by
  induction J with
  | zero => simpa [boundary] using (hasSum_zero (β := ℕ) (α := ℝ))
  | succ J ih =>
      simpa only [boundary, Finset.sum_range_succ, Rat.cast_add] using
        ih.add (hasSum_rowCoeff (H J) (J + 1) (by omega))

/-- Exact rational linear form. There is no smallness or nonvanishing assertion. -/
theorem hasSum_kernel (A : ℚ) (H : ℕ → Polynomial ℚ) (J : ℕ) :
    HasSum (fun n : ℕ =>
      kernel A H J n (1 / ((n + 2).factorial : ℝ)) /
        (((n + 2).factorial : ℝ) - 1))
      ((A : ℝ) * (∑' n : ℕ, Erdos68Development.term n) -
        ((boundary H J : ℚ) : ℝ)) := by
  simpa only [kernel_div, Erdos68Development.term, mul_one_div] using
    (Erdos68Development.summable_term.hasSum.mul_left (A : ℝ)).sub (hasSum_rows H J)


/-- Only A and the boundary sum need be integral; the other coefficients
may remain rational with arbitrary denominators. -/
theorem hasSum_integral_boundary (A B : ℤ) (H : ℕ → Polynomial ℚ) (J : ℕ)
    (hB : boundary H J = B) :
    HasSum (fun n : ℕ =>
      kernel (A : ℚ) H J n (1 / ((n + 2).factorial : ℝ)) /
        (((n + 2).factorial : ℝ) - 1))
      ((A : ℝ) * (∑' n : ℕ, Erdos68Development.term n) - B) := by
  simpa only [hB, Rat.cast_intCast] using hasSum_kernel (A : ℚ) H J

/-- The row n=2 gives a lower bound independent of all polynomial heights. -/
theorem square_kernel_lower_bound (A : ℚ) (hA : 0 ≤ A)
    (H : ℕ → Polynomial ℚ) (J : ℕ) (r : ℕ → ℝ)
    (hK : ∀ n : ℕ,
      kernel A H J n (1 / ((n + 2).factorial : ℝ)) =
        (A : ℝ) * (1 / ((n + 2).factorial : ℝ)) ^ J +
          (1 - 1 / ((n + 2).factorial : ℝ)) * (r n)^2) :
    (A : ℝ) / 2^J ≤
      (A : ℝ) * (∑' n : ℕ, Erdos68Development.term n) - (boundary H J : ℝ) := by
  have hs := hasSum_kernel A H J
  have ha : (0 : ℝ) ≤ A := by exact_mod_cast hA
  have hnonneg (n : ℕ) : 0 ≤
      kernel A H J n (1 / ((n + 2).factorial : ℝ)) /
        (((n + 2).factorial : ℝ) - 1) := by
    rw [hK n]
    apply div_nonneg _ (Erdos68Development.denom_pos n).le
    apply add_nonneg (by positivity)
    exact mul_nonneg (sub_nonneg.mpr
      (Erdos68Development.reciprocal_factorial_lt_one n).le) (sq_nonneg _)
  have hrow := hs.summable.le_tsum 0 (fun n _ => hnonneg n)
  rw [hs.tsum_eq] at hrow
  apply le_trans _ hrow
  rw [hK 0]
  norm_num only [Nat.zero_add, Nat.factorial, Nat.cast_ofNat, Nat.cast_mul,
    Nat.cast_one, sub_self, sub_zero, div_one]
  rw [div_pow, one_pow]
  rw [mul_one_div]
  exact le_add_of_nonneg_right (by positivity)

open Polynomial in
noncomputable def examplePolynomial : Polynomial ℚ :=
  C (1/10) * (-X^2 - C 7*X + C 18)

lemma example_boundary : boundary (fun _ => examplePolynomial) 1 = 1 := by
  norm_num [boundary, examplePolynomial]

/-- Rational polynomial coefficients can cancel a row whose denominator does
not divide A, even while A and the boundary are both integral. -/
theorem cancellation_without_divisibility :
    boundary (fun _ => examplePolynomial) 1 = 1 ∧
    kernel 1 (fun _ => examplePolynomial) 1 0 (1/2) = 0 ∧
    kernel 1 (fun _ => examplePolynomial) 1 1 (1/6) = 0 ∧
    ¬ (5 : ℤ) ∣ 1 := by
  norm_num [boundary, kernel, rowCoeff, examplePolynomial]

lemma example_sum :
    (∑' n : ℕ,
      kernel 1 (fun _ => examplePolynomial) 1 n
        (1 / ((n + 2).factorial : ℝ)) / (((n + 2).factorial : ℝ) - 1)) =
      (∑' n : ℕ, Erdos68Development.term n) - 1 := by
  simpa only [example_boundary, Rat.cast_one, one_mul] using
    (hasSum_kernel 1 (fun _ => examplePolynomial) 1).tsum_eq

#print axioms hasSum_integral_boundary
#print axioms square_kernel_lower_bound
#print axioms cancellation_without_divisibility
#print axioms example_sum


private noncomputable def forcedNode (A B : ℚ) : ℕ → ℚ
  | 0 => B
  | n + 1 => (n + 2 : ℚ) * forcedNode A B n -
      A * (n + 2).factorial / ((n + 2).factorial - 1 : ℚ)

/-- With unrestricted rational coefficients, any finite set of initial rows
can vanish for arbitrary prescribed A and boundary B. -/
theorem finite_rows_zero_arbitrary_rationals (A B : ℚ) (N : ℕ) :
    ∃ H : Polynomial ℚ, H.eval 1 = B ∧
      ∀ n < N, kernel A (fun _ => H) 1 n
        (1 / ((n + 2).factorial : ℝ)) = 0 := by
  let v : ℕ → ℚ := fun n => if n = 0 then 0 else forcedNode A B (n - 1)
  let H := Lagrange.interpolate (Finset.range (N + 2)) (fun n : ℕ => (n : ℚ)) v
  have he (n : ℕ) (hn : n < N + 2) : H.eval (n : ℚ) = v n := by
    apply Lagrange.eval_interpolate_at_node v _ (Finset.mem_range.mpr hn)
    intro i hi j hj hij
    exact_mod_cast hij
  refine ⟨H, ?_, ?_⟩
  · simpa [v, forcedNode] using he 1 (by omega)
  · intro n hn
    have he1 : H.eval ((n + 1 : ℕ) : ℚ) = forcedNode A B n := by
      simpa [v] using he (n + 1) (by omega)
    have he2 : H.eval ((n + 2 : ℕ) : ℚ) = forcedNode A B (n + 1) := by
      simpa [v] using he (n + 2) (by omega)
    have hnum : rowCoeff H 1 n =
        A * (n + 2).factorial / ((n + 2).factorial - 1 : ℚ) := by
      simp only [rowCoeff, he1, he2, forcedNode, pow_one]
      push_cast
      ring
    unfold kernel
    simp only [Finset.sum_range_one, zero_add, pow_zero, mul_one]
    rw [hnum]
    have hf : ((n + 2).factorial : ℝ) ≠ 0 := by positivity
    have hd : ((n + 2).factorial : ℝ) - 1 ≠ 0 :=
      ne_of_gt (Erdos68Development.denom_pos n)
    push_cast
    field_simp
    ring

#print axioms finite_rows_zero_arbitrary_rationals

end RationalKernelForms
