import Submission.FactorialNodePolynomials
import Submission.PhysicalPositiveKernelExample

/-!
Squaring the previously certified physical positive kernel does not produce
another polynomial telescoping kernel. This auxiliary obstruction is not a
proof or disproof of Erdős 68.
-/

namespace PhysicalKernelSquare

open Polynomial PositiveKernelBoundary KernelNonvanishing KernelPowerObstruction
  FactorialNodePolynomials RationalKernelForms
open Filter

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

noncomputable def quotient : Polynomial ℚ :=
    C (54272689 / 44100000000000000) * X^18 +
    C (-4633909303 / 55125000000000000) * X^17 +
    C (1445988091007 / 551250000000000000) * X^16 +
    C (-13577626530583 / 275625000000000000) * X^15 +
    C (37716874620731 / 61250000000000000) * X^14 +
    C (-977603958166373 / 183750000000000000) * X^13 +
    C (3854785881950273 / 122500000000000000) * X^12 +
    C (-39745769626679 / 344531250000000) * X^11 +
    C (15669543744264661 / 122500000000000000) * X^10 +
    C (42593516362998347 / 34453125000000000) * X^9 +
    C (-4582091791277591249 / 551250000000000000) * X^8 +
    C (334569259654585759 / 13781250000000000) * X^7 +
    C (-94781260206486233 / 4375000000000000) * X^6 +
    C (-176084940462866269 / 1640625000000000) * X^5 +
    C (274251367238861869309 / 551250000000000000) * X^4 +
    C (-273090771358578393281 / 275625000000000000) * X^3 +
    C (12495967390321242791 / 14700000000000000) * X^2 +
    C (363256373755931817811 / 551250000000000000) * X^1 +
    C (-3377460071209352023489 / 1102500000000000000) * X^0

noncomputable def residue : Polynomial ℚ :=
    C (74679600728482924703 / 15312500000000000) * X^3 +
    C (-22585727540270736179 / 45937500000000000) * X^2 +
    C (-1054451535662902537 / 1837500000000000) * X^1 +
    C (-60373964036693728681 / 22968750000000000) * X^0

lemma columnOperator_sub (P Q : Polynomial ℚ) (j : ℕ) :
    columnOperator (P - Q) j = columnOperator P j - columnOperator Q j := by
  simp only [columnOperator, sub_comp]
  ring

/-- Exact rational polynomial division certificate. -/
lemma square_column_decomposition :
    (columnOperator PhysicalPositiveKernelExample.upper 1) ^ 2 =
      columnOperator quotient 3 + residue := by
  apply Polynomial.funext
  intro x
  norm_num [columnOperator, PhysicalPositiveKernelExample.upper, quotient, residue]
  ring

lemma residue_degree : residue.natDegree ≤ 3 := by
  unfold residue
  compute_degree

lemma residue_ne_zero : residue ≠ 0 := by
  intro hz
  have he := congrArg (eval (0 : ℚ)) hz
  norm_num [residue] at he

/-- The fourth-power column required by the square is not in the column image. -/
theorem square_column_not_image (H : Polynomial ℚ) :
    columnOperator H 3 ≠ (columnOperator PhysicalPositiveKernelExample.upper 1) ^ 2 := by
  intro he
  have hh : columnOperator (H - quotient) 3 = residue := by
    rw [columnOperator_sub, he, square_column_decomposition]
    ring
  have hne : H - quotient ≠ 0 := by
    intro hz
    apply residue_ne_zero
    simpa [hz, columnOperator] using hh.symm
  have hd := natDegree_columnOperator (H - quotient) hne 3
  rw [hh] at hd
  have hr := residue_degree
  omega

noncomputable def physical : Bivariate :=
  formalKernel 4 PhysicalPositiveKernelExample.family 2

lemma physical_expansion : physical =
    C (C 4 - columnOperator PhysicalPositiveKernelExample.lower 0) +
    C (columnOperator PhysicalPositiveKernelExample.lower 0 -
      columnOperator PhysicalPositiveKernelExample.upper 1) * X +
    C (columnOperator PhysicalPositiveKernelExample.upper 1) * X ^ 2 := by
  simp only [physical, formalKernel, columnSum, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one,
    PhysicalPositiveKernelExample.family, ite_true, Nat.one_ne_zero,
    if_false, map_sub]
  ring

lemma upper_column_ne_zero : columnOperator PhysicalPositiveKernelExample.upper 1 ≠ 0 := by
  intro hz
  have he := congrArg (eval (0 : ℚ)) hz
  norm_num [columnOperator_zero, PhysicalPositiveKernelExample.upper] at he

lemma physical_top_coeff : physical.coeff 2 =
    columnOperator PhysicalPositiveKernelExample.upper 1 := by
  rw [physical_expansion]
  norm_num [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X]

lemma physical_degree : physical.natDegree = 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [physical_expansion]
    compute_degree
  · rw [physical_top_coeff]
    exact upper_column_ne_zero

lemma physical_leadingCoeff : physical.leadingCoeff =
    columnOperator PhysicalPositiveKernelExample.upper 1 := by
  rw [leadingCoeff, physical_degree, physical_top_coeff]

/-- Even the known positive example cannot simply be squared and reused. -/
theorem square_not_kernel (B : ℚ) (H : ℕ → Polynomial ℚ) (J : ℕ) :
    physical ^ 2 ≠ formalKernel B H J := by
  intro he
  have hd : (formalKernel B H J).natDegree = 3 + 1 := by
    rw [← he, natDegree_pow, physical_degree]
  obtain ⟨K, hK⟩ := highest_coefficient_in_image B H J 3 hd
  have hc : (formalKernel B H J).coeff (3 + 1) =
      (columnOperator PhysicalPositiveKernelExample.upper 1) ^ 2 := by
    calc
      _ = (formalKernel B H J).leadingCoeff := by rw [leadingCoeff, hd]
      _ = _ := by rw [← he, leadingCoeff_pow, physical_leadingCoeff]
  exact square_column_not_image K (hK.trans hc)

/-- This failure persists at every sufficiently late factorial node. -/
theorem eventually_square_ne_kernel (B : ℚ) (H : ℕ → Polynomial ℚ) (J : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (kernel 4 PhysicalPositiveKernelExample.family 2 n
        (1 / ((n + 2).factorial : ℝ))) ^ 2 ≠
      kernel B H J n (1 / ((n + 2).factorial : ℝ)) := by
  have ht := eventually_node_ne_zero (physical ^ 2 - formalKernel B H J)
    (sub_ne_zero.mpr (square_not_kernel B H J))
  filter_upwards [ht] with n hn
  have he : nodeEval (physical ^ 2 - formalKernel B H J) n =
      (nodeEval physical n) ^ 2 - nodeEval (formalKernel B H J) n := by
    simp [nodeEval, eval₂_pow]
  rw [he, physical, nodeEval_formalKernel, nodeEval_formalKernel, sub_ne_zero] at hn
  exact hn

end PhysicalKernelSquare

#print axioms PhysicalKernelSquare.square_column_decomposition
#print axioms PhysicalKernelSquare.square_not_kernel
#print axioms PhysicalKernelSquare.eventually_square_ne_kernel
