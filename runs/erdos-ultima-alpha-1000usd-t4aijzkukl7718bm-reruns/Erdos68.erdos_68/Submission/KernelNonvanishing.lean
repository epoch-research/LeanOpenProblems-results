import Submission.PositiveKernelBoundary

/-!
A fixed rational polynomial kernel with nonzero retained coefficient cannot
vanish at all sufficiently large factorial nodes. Consequently nonnegative
kernels give strictly positive linear forms. This supplies no upper bound or
integral-boundary construction, and does not settle Erdős 68.
-/

namespace KernelNonvanishing

open Filter Polynomial RationalKernelForms PositiveKernelBoundary
open scoped Topology

/-- The column operator raises the degree of every nonzero polynomial. -/
lemma natDegree_columnOperator (H : Polynomial ℚ) (hH : H ≠ 0) (j : ℕ) :
    (columnOperator H j).natDegree = H.natDegree + (j+1) := by
  have hc : H.comp (X - C 1) ≠ 0 := by
    simpa only [sub_eq_add_neg, ← map_neg] using
      (comp_X_add_C_ne_zero_iff (p := H) (t := (-1 : ℚ))).mpr hH
  have hd : (X ^ (j+1) * H.comp (X - C 1)).natDegree = H.natDegree + (j+1) := by
    rw [natDegree_X_pow_mul (j+1) hc, natDegree_comp, natDegree_X_sub_C, mul_one]
  rw [columnOperator, natDegree_sub_eq_left_of_natDegree_lt (by rw [hd]; omega), hd]

lemma columnOperator_eq_constant (H : Polynomial ℚ) (j : ℕ) (A : ℚ)
    (he : columnOperator H j = C A) : A = 0 := by
  by_cases hz : H = 0
  · simpa [hz, columnOperator] using he.symm
  · have hd := natDegree_columnOperator H hz j
    rw [he, natDegree_C] at hd
    omega

lemma tendsto_row_mul_recip_pow (H : Polynomial ℚ) (j k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => (rowCoeff H (j+1) n : ℝ) *
      (1 / ((n+2).factorial : ℝ)) ^ k) atTop (𝓝 0) := by
  have hs := summable_eval_div_factorial_pow (columnOperator H j) k hk
  have hs' := (summable_nat_add_iff 2).mpr hs
  simpa only [columnOperator_eval_row, div_pow, one_pow, mul_one_div] using
    hs'.tendsto_atTop_zero

lemma tendsto_recip_factorial :
    Tendsto (fun n : ℕ => 1 / ((n+2).factorial : ℝ)) atTop (𝓝 0) := by
  have hs := summable_eval_div_factorial_pow (C 1) 1 (by omega)
  have hs' := (summable_nat_add_iff 2).mpr hs
  simpa using hs'.tendsto_atTop_zero

lemma tendsto_kernel_remainder (A : ℚ) (H : ℕ → Polynomial ℚ) (J : ℕ) :
    Tendsto (fun n : ℕ => kernel A H (J+1) n (1 / ((n+2).factorial : ℝ)) -
      ((A : ℝ) - (rowCoeff (H 0) 1 n : ℝ))) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range J,
      (rowCoeff (H (j+1)) (j+1+1) n : ℝ) *
        (1 / ((n+2).factorial : ℝ)) ^ (j+1)) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum (Finset.range J) (fun j _ =>
      tendsto_row_mul_recip_pow (H (j+1)) (j+1) (j+1) (by omega))
  have ht := (tendsto_row_mul_recip_pow (H 0) 0 1 (by omega)).sub
    (((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_recip_factorial).mul hs)
  convert ht using 1
  · funext n
    simp only [kernel, Finset.sum_range_succ', pow_zero, pow_one, mul_one]
    ring
  · simp

lemma polynomial_abs_eventually_ge (P : Polynomial ℝ) (hP : P ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c ≤ |P.eval ((n+2 : ℕ) : ℝ)| := by
  by_cases hd : P.degree ≤ 0
  · have he := eq_C_of_degree_le_zero hd
    have hc : P.coeff 0 ≠ 0 := by
      intro hz
      rw [he, hz, C_0] at hP
      exact hP rfl
    refine ⟨|P.coeff 0|, abs_pos.mpr hc, Filter.Eventually.of_forall ?_⟩
    intro n
    conv_rhs => rw [he, eval_C]
  · refine ⟨1, by norm_num, ?_⟩
    have hlim := (P.abs_tendsto_atTop (lt_of_not_ge hd)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
    exact (tendsto_atTop.mp hlim) 1

/-- Every fixed nontrivial rational polynomial kernel is nonzero at all
sufficiently late factorial nodes. -/
theorem eventually_kernel_ne_zero (A : ℚ) (hA : A ≠ 0)
    (H : ℕ → Polynomial ℚ) (J : ℕ) :
    ∀ᶠ n : ℕ in atTop, kernel A H J n (1 / ((n+2).factorial : ℝ)) ≠ 0 := by
  cases J with
  | zero =>
      have ha : (A : ℝ) ≠ 0 := by exact_mod_cast hA
      exact Filter.Eventually.of_forall (fun n => by simpa [kernel] using ha)
  | succ J =>
      let Q := C A - columnOperator (H 0) 0
      have hQ : Q ≠ 0 := by
        intro hz
        have he : columnOperator (H 0) 0 = C A := (sub_eq_zero.mp hz).symm
        exact hA (columnOperator_eq_constant (H 0) 0 A he)
      let P := Q.map (Rat.castHom ℝ)
      have hP : P ≠ 0 := (Polynomial.map_ne_zero_iff (Rat.castHom ℝ).injective).mpr hQ
      have heval (n : ℕ) : P.eval ((n+2 : ℕ) : ℝ) =
          (A : ℝ) - (rowCoeff (H 0) 1 n : ℝ) := by
        have he := eval_map_apply (f := Rat.castHom ℝ) (p := Q) ((n+2 : ℕ) : ℚ)
        change P.eval (((n+2 : ℕ) : ℚ) : ℝ) = ((Q.eval ((n+2 : ℕ) : ℚ) : ℚ) : ℝ) at he
        simpa only [Rat.cast_natCast, Q, eval_sub, eval_C,
          columnOperator_eval_row, Rat.cast_sub] using he
      obtain ⟨c, hc, hb⟩ := polynomial_abs_eventually_ge P hP
      have hr := (tendsto_order.mp
        (tendsto_kernel_remainder A H J).abs).2 c (by simpa using hc)
      filter_upwards [hb, hr] with n hn he
      intro hz
      rw [hz, zero_sub, abs_neg, ← heval n] at he
      exact (not_lt_of_ge hn) he

/-- Positivity at the actual factorial nodes alone ensures strict positivity
of the total error; no specified positive row is needed. -/
theorem positive_form_of_kernel_nonneg (A : ℚ) (hA : A ≠ 0)
    (H : ℕ → Polynomial ℚ) (J : ℕ)
    (hK : ∀ n : ℕ, 0 ≤ kernel A H J n (1 / ((n+2).factorial : ℝ))) :
    0 < (A : ℝ) * (∑' n : ℕ, Erdos68Development.term n) - (boundary H J : ℝ) := by
  obtain ⟨n, hn⟩ := (eventually_kernel_ne_zero A hA H J).exists
  have hs := hasSum_kernel A H J
  rw [← hs.tsum_eq]
  apply hs.summable.tsum_pos
  · intro m
    exact div_nonneg (hK m) (Erdos68Development.denom_pos m).le
  · exact div_pos (lt_of_le_of_ne (hK n) (Ne.symm hn))
      (Erdos68Development.denom_pos n)

end KernelNonvanishing

#print axioms KernelNonvanishing.eventually_kernel_ne_zero
#print axioms KernelNonvanishing.positive_form_of_kernel_nonneg
