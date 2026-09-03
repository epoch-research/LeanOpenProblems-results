import Submission.LambertBoundaryClearing

/-!
Exact factor division does not preserve integrality of the actual Lambert
boundaries, even when a full period of output phases has been cleared.
This auxiliary example does not settle Erdős Problem 68.
-/

namespace LambertFactorDivisionBoundary

open LambertBoundaryClearing LambertDifferenceOperators

private lemma coeff_0 : Erdos68Development.lambertCoeff 0 = 0 := by decide

private lemma coeff_1 : Erdos68Development.lambertCoeff 1 = 0 := by decide

private lemma coeff_2 : Erdos68Development.lambertCoeff 2 = 1 := by decide

private lemma coeff_3 : Erdos68Development.lambertCoeff 3 = 1 := by decide

private lemma coeff_4 : Erdos68Development.lambertCoeff 4 = 7 := by decide

private lemma coeff_5 : Erdos68Development.lambertCoeff 5 = 1 := by decide

private lemma coeff_6 : Erdos68Development.lambertCoeff 6 = 111 := by decide

private lemma coeff_7 : Erdos68Development.lambertCoeff 7 = 1 := by decide

private lemma coeff_8 : Erdos68Development.lambertCoeff 8 = 2591 := by decide

private lemma coeff_9 : Erdos68Development.lambertCoeff 9 = 1681 := by decide

private lemma coeff_10 : Erdos68Development.lambertCoeff 10 = 113653 := by decide

private lemma coeff_11 : Erdos68Development.lambertCoeff 11 = 1 := by decide

private lemma coeff_12 : Erdos68Development.lambertCoeff 12 = 7889575 := by decide

lemma factored_boundary_seven :
    (26611200 : ℚ) * boundary [3] 7 = 165160732 := by
  norm_num [boundary, rawApplyQ, prefixQ, Finset.sum_range_succ,
    coeff_0, coeff_1, coeff_2, coeff_3, coeff_4, coeff_5, coeff_6, coeff_7, coeff_8, coeff_9, coeff_10, coeff_11, coeff_12, Nat.factorial]

lemma factored_boundary_eight :
    (26611200 : ℚ) * boundary [3] 8 = 163450676 := by
  norm_num [boundary, rawApplyQ, prefixQ, Finset.sum_range_succ,
    coeff_0, coeff_1, coeff_2, coeff_3, coeff_4, coeff_5, coeff_6, coeff_7, coeff_8, coeff_9, coeff_10, coeff_11, coeff_12, Nat.factorial]

lemma factored_boundary_nine :
    (26611200 : ℚ) * boundary [3] 9 = 165957261 := by
  norm_num [boundary, rawApplyQ, prefixQ, Finset.sum_range_succ,
    coeff_0, coeff_1, coeff_2, coeff_3, coeff_4, coeff_5, coeff_6, coeff_7, coeff_8, coeff_9, coeff_10, coeff_11, coeff_12, Nat.factorial]

lemma quotient_boundary_nine :
    (26611200 : ℚ) * boundary [] 9 = 94996000 / 3 := by
  norm_num [boundary, rawApplyQ, prefixQ, Finset.sum_range_succ,
    coeff_0, coeff_1, coeff_2, coeff_3, coeff_4, coeff_5, coeff_6, coeff_7, coeff_8, coeff_9, coeff_10, coeff_11, coeff_12, Nat.factorial]

lemma full_period_integral :
    ∀ n ∈ Finset.Icc 7 9, ∃ z : ℤ,
      (26611200 : ℚ) * boundary [3] n = z := by
  intro n hn
  have h := Finset.mem_Icc.mp hn
  have he : n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases he with rfl | rfl | rfl
  · exact ⟨165160732, factored_boundary_seven⟩
  · exact ⟨163450676, factored_boundary_eight⟩
  · exact ⟨165957261, factored_boundary_nine⟩

lemma quotient_not_integral :
    ¬ ∃ z : ℤ, (26611200 : ℚ) * boundary [] 9 = z := by
  rw [quotient_boundary_nine]
  rintro ⟨z, hz⟩
  have hq : (3 : ℚ) * (z : ℚ) = 94996000 := by linarith
  have hz' : (3 : ℤ) * z = 94996000 := by exact_mod_cast hq
  omega

/-- There is an actual cleared full-period boundary whose exact row-factor
quotient is not cleared by the same multiplier. -/
theorem exact_factor_division_loses_integrality :
    ∃ C : ℕ, 0 < C ∧
      (∀ n ∈ Finset.Icc 7 9, ∃ z : ℤ, (C : ℚ) * boundary [3] n = z) ∧
      ¬ (∀ n ∈ Finset.Icc 7 9, ∃ z : ℤ, (C : ℚ) * boundary [] n = z) := by
  refine ⟨26611200, by norm_num, full_period_integral, ?_⟩
  intro h
  exact quotient_not_integral (h 9 (by decide))

end LambertFactorDivisionBoundary

#print axioms LambertFactorDivisionBoundary.exact_factor_division_loses_integrality
