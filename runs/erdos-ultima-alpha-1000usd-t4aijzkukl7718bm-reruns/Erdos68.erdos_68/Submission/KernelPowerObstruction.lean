import Submission.KernelNonvanishing

/-!
The rational polynomial telescoping kernels are not closed under pointwise
powers. This is auxiliary algebra, not a settlement of Erdős 68.
-/

namespace KernelPowerObstruction

open Polynomial PositiveKernelBoundary KernelNonvanishing

noncomputable section

/-- The inner variable is the original row index; the outer variable is `t`. -/
abbrev Bivariate := Polynomial (Polynomial ℚ)

def columnSum (H : ℕ → Polynomial ℚ) (J : ℕ) : Bivariate :=
  ∑ j ∈ Finset.range J, C (columnOperator (H j) j) * X ^ j

def formalKernel (A : ℚ) (H : ℕ → Polynomial ℚ) (J : ℕ) : Bivariate :=
  C (C A) - (1 - X) * columnSum H J

def basicKernel (A : ℚ) : Bivariate :=
  C (C A) - (1 - X) * C ((X : Polynomial ℚ) - 1)

lemma columnSum_coeff (H : ℕ → Polynomial ℚ) (J j : ℕ) :
    (columnSum H J).coeff j = if j < J then columnOperator (H j) j else 0 := by
  classical
  simp [columnSum, finset_sum_coeff]

lemma columnOperator_C (c : ℚ) (j : ℕ) :
    columnOperator (C c) j = C c * (X ^ (j + 1) - 1) := by
  simp only [columnOperator, C_comp]
  ring

lemma basic_is_kernel (A : ℚ) :
    formalKernel A (fun _ => 1) 1 = basicKernel A := by
  simp [formalKernel, columnSum, basicKernel, columnOperator]

/-- The highest column needed by a nontrivial power is not a telescoping column. -/
theorem power_not_column (j : ℕ) (hj : 1 ≤ j) (H : Polynomial ℚ) :
    columnOperator H j ≠ (X - 1) ^ (j + 1) := by
  intro he
  have hp : (X - 1 : Polynomial ℚ) ≠ 0 := by
    intro hz
    have := congrArg (fun p : Polynomial ℚ => p.coeff 1) hz
    norm_num [coeff_one] at this
  have hH : H ≠ 0 := by
    intro hz
    have : (X - 1 : Polynomial ℚ) ^ (j + 1) = 0 := by
      simpa [hz, columnOperator] using he.symm
    exact pow_ne_zero _ hp this
  have hd := natDegree_columnOperator H hH j
  rw [he, natDegree_pow, show (X - 1 : Polynomial ℚ).natDegree = 1 by
    simpa using natDegree_X_sub_C (1 : ℚ), mul_one] at hd
  have hdeg : H.natDegree = 0 := by omega
  rw [eq_C_of_natDegree_eq_zero hdeg, columnOperator_C] at he
  have hc := congrArg (fun p : Polynomial ℚ => p.coeff j) he
  dsimp only at hc
  have hj0 : j ≠ 0 := by omega
  have hjs : j ≠ j + 1 := by omega
  have hex : (X - 1 : Polynomial ℚ) = X + C (-1) := by simp only [map_neg, map_one]; ring
  rw [hex, coeff_X_add_C_pow] at hc
  simp only [coeff_C_mul, coeff_sub, coeff_X_pow, if_neg hjs,
    coeff_one, if_neg hj0, sub_zero, mul_zero,
    Nat.add_sub_cancel_left, pow_one] at hc
  have hpos : (0 : ℚ) < (j + 1 : ℕ) := by positivity
  norm_num at hc
  linarith

lemma one_sub_X_degree : (1 - X : Bivariate).natDegree = 1 := by
  have he : (1 - X : Bivariate) = -(X - C 1) := by simp
  rw [he, natDegree_neg, natDegree_X_sub_C]

lemma columnSum_top_degree (A : ℚ) (H : ℕ → Polynomial ℚ) (J m : ℕ)
    (hd : (formalKernel A H J).natDegree = m + 1) :
    (columnSum H J).natDegree = m := by
  have hq : columnSum H J ≠ 0 := by
    intro hz
    simp [formalKernel, hz] at hd
  have hprod : ((1 - X) * columnSum H J).natDegree =
      (columnSum H J).natDegree + 1 := by
    rw [natDegree_mul (by
      intro hz
      have hh := one_sub_X_degree
      rw [hz, natDegree_zero] at hh
      omega) hq, one_sub_X_degree]
    omega
  have hf : (formalKernel A H J).natDegree = (columnSum H J).natDegree + 1 := by
    unfold formalKernel
    rw [natDegree_sub_eq_right_of_natDegree_lt (by rw [natDegree_C, hprod]; omega),
      hprod]
  omega

/-- A polynomial kernel's highest outer coefficient must lie in its column image. -/
theorem highest_coefficient_in_image (A : ℚ) (H : ℕ → Polynomial ℚ) (J m : ℕ)
    (hd : (formalKernel A H J).natDegree = m + 1) :
    ∃ K : Polynomial ℚ,
      columnOperator K m = (formalKernel A H J).coeff (m + 1) := by
  classical
  have hqdeg := columnSum_top_degree A H J m hd
  have hzero : (columnSum H J).coeff (m + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hc : (formalKernel A H J).coeff (m + 1) = (columnSum H J).coeff m := by
    unfold formalKernel
    rw [sub_mul, one_mul, coeff_sub, coeff_sub, coeff_C_succ, coeff_X_mul,
      hzero]
    ring
  rw [hc, columnSum_coeff]
  split_ifs with hm
  · exact ⟨H m, rfl⟩
  · exact ⟨0, by simp [columnOperator]⟩

lemma basicKernel_degree (A : ℚ) : (basicKernel A).natDegree = 1 := by
  have hp : (X - 1 : Polynomial ℚ) ≠ 0 := by
    intro hz
    have := congrArg (fun p : Polynomial ℚ => p.coeff 1) hz
    norm_num [coeff_one] at this
  have hprod : ((1 - X) * C ((X : Polynomial ℚ) - 1)).natDegree = 1 := by
    rw [natDegree_mul_C hp, one_sub_X_degree]
  unfold basicKernel
  rw [natDegree_sub_eq_right_of_natDegree_lt (by rw [natDegree_C, hprod]; omega), hprod]

lemma basicKernel_leadingCoeff (A : ℚ) : (basicKernel A).leadingCoeff = X - 1 := by
  rw [leadingCoeff, basicKernel_degree]
  unfold basicKernel
  rw [sub_mul, one_mul]
  simp [coeff_one, coeff_sub, coeff_X_mul]

/-- No power of degree at least two of this elementary kernel is a formal
polynomial telescoping kernel, even with unrestricted rational coefficients
and arbitrarily many columns. -/
theorem basic_power_not_kernel (A B : ℚ) (j : ℕ) (hj : 1 ≤ j)
    (H : ℕ → Polynomial ℚ) (J : ℕ) :
    (basicKernel A) ^ (j + 1) ≠ formalKernel B H J := by
  intro he
  have hd : (formalKernel B H J).natDegree = j + 1 := by
    rw [← he, natDegree_pow, basicKernel_degree, mul_one]
  obtain ⟨K, hK⟩ := highest_coefficient_in_image B H J j hd
  have hc : (formalKernel B H J).coeff (j + 1) = (X - 1) ^ (j + 1) := by
    calc
      _ = (formalKernel B H J).leadingCoeff := by rw [leadingCoeff, hd]
      _ = _ := by rw [← he, leadingCoeff_pow, basicKernel_leadingCoeff]
  exact power_not_column j hj K (hK.trans hc)

end

end KernelPowerObstruction

#print axioms KernelPowerObstruction.power_not_column
#print axioms KernelPowerObstruction.highest_coefficient_in_image
#print axioms KernelPowerObstruction.basic_power_not_kernel
