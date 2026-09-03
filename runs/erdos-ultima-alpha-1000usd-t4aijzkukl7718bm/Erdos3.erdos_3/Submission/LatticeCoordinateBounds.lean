import Submission.LatticePrecisionBudget

/-! Individual primal length bounds and a lower bound on the norm of every
nonzero integral dual functional. These use the product of basis lengths. -/
namespace Erdos3LatticeCoordinateBounds
open Finset Module Erdos3LatticePhaseCoordinates
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma length_le_product (b : Basis I ℝ E) (hmin : ∀ i, 1 ≤ ‖b i‖) (i : I) :
    ‖b i‖ ≤ ∏ j, ‖b j‖ := by
  calc
    _ = ‖b i‖*1 := (mul_one _).symm
    _ ≤ ‖b i‖*(∏ j ∈ univ.erase i, ‖b j‖) :=
      mul_le_mul_of_nonneg_left (one_le_prod _ hmin) (norm_nonneg _)
    _ = _ := mul_prod_erase univ (fun j ↦ ‖b j‖) (mem_univ i)

lemma exists_nonzero_basis_value (b : Basis I ℝ E) (F : E →L[ℝ] ℝ) (hF : F ≠ 0) :
    ∃ i, F (b i) ≠ 0 := by
  by_contra hh
  push_neg at hh
  apply hF
  ext x
  calc
    F x = F (∑ i, b.repr x i • b i) := by rw [b.sum_repr]
    _ = 0 := by simp only [map_sum,map_smul,hh,smul_zero,sum_const_zero]

lemma integral_dual_norm_lower (b : Basis I ℝ E) (F : E →L[ℝ] ℝ) (hF : F ≠ 0)
    (hint : ∀ y : E, y ∈ Submodule.span ℤ (Set.range b) → ∃ c : ℤ, F y = (c:ℝ))
    (U : ℕ) (hb : ∀ i, ‖b i‖ ≤ (2:ℝ)^U) : (1/2:ℝ)^U ≤ ‖F‖ := by
  obtain ⟨i,hi⟩ := exists_nonzero_basis_value b F hF
  obtain ⟨c,hc⟩ := hint (b i) (Submodule.subset_span (Set.mem_range_self i))
  have hc0 : c ≠ 0 := by intro hz; simp [hc,hz] at hi
  have h1 : (1:ℝ) ≤ |F (b i)| := by rw [hc]; exact_mod_cast Int.one_le_abs hc0
  have h2 : |F (b i)| ≤ ‖F‖*(2:ℝ)^U := by
    calc
      _ ≤ ‖F‖*‖b i‖ := by simpa only [Real.norm_eq_abs] using F.le_opNorm (b i)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _)
  rw [div_pow,one_pow]
  exact (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ) < 2) U)).mpr (h1.trans h2)

lemma integral_dual_norm_lower_of_product (b : Basis I ℝ E)
    (hmin : ∀ i, 1 ≤ ‖b i‖) (U : ℕ) (hprod : (∏ i, ‖b i‖) ≤ (2:ℝ)^U)
    (F : E →L[ℝ] ℝ) (hF : F ≠ 0)
    (hint : ∀ y : E, y ∈ Submodule.span ℤ (Set.range b) → ∃ c : ℤ, F y = (c:ℝ)) :
    (1/2:ℝ)^U ≤ ‖F‖ :=
  integral_dual_norm_lower b F hF hint U (fun i ↦ (length_le_product b hmin i).trans hprod)

#print axioms integral_dual_norm_lower_of_product
end Erdos3LatticeCoordinateBounds
