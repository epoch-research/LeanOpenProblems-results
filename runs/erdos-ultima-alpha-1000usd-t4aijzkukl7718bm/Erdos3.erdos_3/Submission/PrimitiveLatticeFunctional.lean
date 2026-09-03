import Submission.LatticePhaseCoordinates
import Submission.PrimitiveIntegerFrequency

/-! Normalize an integral dual functional to be primitive on an integer lattice.
The functional norm does not increase; its common divisor is retained as a
separate arithmetic factor. -/
namespace Erdos3PrimitiveLatticeFunctional
open Finset Module Erdos3LatticePhaseCoordinates Erdos3PrimitiveIntegerFrequency
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma functional_eq_dualFrequency (b : Basis I ℝ E) (F : E →L[ℝ] ℝ) (h : I → ℤ)
    (hF : ∀ i, F (b i) = (h i : ℝ)) : F = dualFrequency b h := by
  ext x
  calc
    _ = F (∑ i, b.repr x i • b i) := by rw [b.sum_repr]
    _ = ∑ i, (h i : ℝ)*b.repr x i := by
      rw [map_sum]
      apply sum_congr rfl
      intro i _
      rw [map_smul,hF,smul_eq_mul,mul_comm]
    _ = _ := (dualFrequency_apply b h x).symm

/-- A primitive functional takes value one on a lattice vector. Multiplying
it by the positive integer g recovers F, and g is bounded by some basis value. -/
theorem primitive_lattice_functional (b : Basis I ℝ E) (F : E →L[ℝ] ℝ) (hF : F ≠ 0)
    (hint : ∀ y : E, y ∈ Submodule.span ℤ (Set.range b) → ∃ c : ℤ, F y = (c : ℝ)) :
    ∃ g : ℕ, ∃ F₀ : E →L[ℝ] ℝ, ∃ v : E, 0 < g ∧ F = (g : ℝ) • F₀ ∧
      v ∈ Submodule.span ℤ (Set.range b) ∧ F₀ v = 1 ∧
      (∀ y : E, y ∈ Submodule.span ℤ (Set.range b) → ∃ c : ℤ, F₀ y = (c : ℝ)) ∧
      ‖F₀‖ ≤ ‖F‖ ∧ (∃ i, (g : ℝ) ≤ |F (b i)|) := by
  have hb : ∀ i, ∃ c : ℤ, F (b i) = (c : ℝ) := by
    intro i
    exact hint (b i) (Submodule.subset_span (Set.mem_range_self i))
  choose h hh using hb
  have hFeq := functional_eq_dualFrequency b F h hh
  have hne : ∃ i, h i ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hF
    rw [hFeq]
    simp only [dualFrequency,hn,Int.cast_zero,zero_smul,sum_const_zero]
  obtain ⟨g,h₀,c,hg,hh₀,hc,habs,hgB⟩ := primitive_integer_frequency h hne
  let F₀ := dualFrequency b h₀
  let v : E := ∑ i, c i • b i
  have hv : v ∈ Submodule.span ℤ (Set.range b) := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hF₀v : F₀ v = 1 := by
    dsimp only [v,F₀]
    simp only [map_sum,map_zsmul,dualFrequency_basis,zsmul_eq_mul]
    exact_mod_cast hc
  have hsplit : F = (g : ℝ) • F₀ := by
    rw [hFeq]
    dsimp only [dualFrequency,F₀]
    rw [smul_sum]
    apply sum_congr rfl
    intro i _
    rw [hh₀ i,Int.cast_mul,Int.cast_natCast,smul_smul]
  have hnorm : ‖F₀‖ ≤ ‖F‖ := by
    rw [hsplit,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg g : (0 : ℝ) ≤ g)]
    have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hg1 (norm_nonneg F₀)
  have hgval : ∃ i, (g : ℝ) ≤ |F (b i)| := by
    obtain ⟨i,hi⟩ := hne
    refine ⟨i,?_⟩
    rw [hh i]
    have hiB := hgB i hi
    have hz : (g : ℤ) ≤ |h i| := by simpa only [Int.natCast_natAbs] using (show (g : ℤ) ≤ ((h i).natAbs : ℤ) by exact_mod_cast hiB)
    exact_mod_cast hz
  exact ⟨g,F₀,v,hg,hsplit,hv,hF₀v,fun y hy ↦ dualFrequency_integral b h₀ y hy,hnorm,hgval⟩

#print axioms primitive_lattice_functional
end Erdos3PrimitiveLatticeFunctional
