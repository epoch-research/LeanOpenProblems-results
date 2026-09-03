import Submission.AnisotropicPolynomialObstruction

/-! Coordinate phase rounding and integral dual frequencies for the integer
span of a finite real basis. No lattice reduction theorem is assumed here. -/
namespace Erdos3LatticePhaseCoordinates
open Finset Module Erdos3CircleIntegerApproximation
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def coordinate (b : Basis I ℝ E) (i : I) : E →L[ℝ] ℝ :=
  (b.coord i).toContinuousLinearMap

lemma coordinate_apply (b : Basis I ℝ E) (i : I) (x : E) : coordinate b i x = b.repr x i := rfl
lemma coordinate_basis (b : Basis I ℝ E) (i j : I) : coordinate b i (b j) = if i=j then 1 else 0 := by
  simp only [coordinate_apply,Basis.repr_self,Finsupp.single_apply,eq_comm]

noncomputable def dualFrequency (b : Basis I ℝ E) (h : I → ℤ) : E →L[ℝ] ℝ :=
  ∑ i, (h i : ℝ) • coordinate b i

lemma dualFrequency_apply (b : Basis I ℝ E) (h : I → ℤ) (x : E) :
    dualFrequency b h x = ∑ i, (h i : ℝ)*(b.repr x i) := by
  simp only [dualFrequency,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,coordinate_apply]

lemma dualFrequency_basis (b : Basis I ℝ E) (h : I → ℤ) (i : I) :
    dualFrequency b h (b i) = (h i : ℝ) := by
  simp [dualFrequency_apply,Basis.repr_self,Finsupp.single_apply]

lemma dualFrequency_ne_zero (b : Basis I ℝ E) (h : I → ℤ) (hne : ∃ i, h i ≠ 0) :
    dualFrequency b h ≠ 0 := by
  intro hh
  obtain ⟨i,hi⟩ := hne
  have he := dualFrequency_basis b h i
  rw [hh,ContinuousLinearMap.zero_apply] at he
  exact hi (by exact_mod_cast he.symm)

lemma dualFrequency_integral (b : Basis I ℝ E) (h : I → ℤ) (x : E)
    (hx : x ∈ Submodule.span ℤ (Set.range b)) :
    ∃ a : ℤ, dualFrequency b h x = (a : ℝ) := by
  have hc : ∀ i, ∃ c : ℤ, (c : ℝ) = b.repr x i := by
    intro i
    exact (b.mem_span_iff_repr_mem ℤ x).mp hx i
  choose c hc using hc
  refine ⟨∑ i, h i*c i,?_⟩
  rw [dualFrequency_apply]
  simp only [← hc,Int.cast_sum,Int.cast_mul]

lemma dualFrequency_norm (b : Basis I ℝ E) (h : I → ℤ) (B : I → ℝ)
    (hB : ∀ i, |(h i : ℝ)| ≤ B i) :
    ‖dualFrequency b h‖ ≤ ∑ i, B i*‖coordinate b i‖ := by
  calc
    _ ≤ ∑ i, ‖(h i : ℝ) • coordinate b i‖ := norm_sum_le _ _
    _ = ∑ i, |(h i : ℝ)| *‖coordinate b i‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ _ := sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_right (hB i) (norm_nonneg _))

/-- Small coordinate chords give a nearby point of the integer span of b,
with the norm error weighted by the lengths of the basis vectors. -/
theorem exists_lattice_near_of_chords (b : Basis I ℝ E) (x : E) (ε : I → ℝ)
    (hphase : ∀ i, ‖ephase (b.repr x i)-1‖ ≤ ε i) :
    ∃ y : E, y ∈ Submodule.span ℤ (Set.range b) ∧
      ‖x-y‖ ≤ (∑ i, ε i*‖b i‖)/4 := by
  have hc : ∀ i, ∃ c : ℤ, |b.repr x i-(c : ℝ)| ≤ ε i/4 := by
    intro i
    obtain ⟨c,hc⟩ := exists_integer_near (b.repr x i)
    exact ⟨c,hc.trans (div_le_div_of_nonneg_right (hphase i) (by norm_num))⟩
  choose c hc using hc
  let y : E := ∑ i, c i • b i
  have hy : y ∈ Submodule.span ℤ (Set.range b) := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have he : x-y = ∑ i, (b.repr x i-(c i : ℝ)) • b i := by
    calc
      _ = (∑ i, (b.repr x i) • b i)-(∑ i, (c i : ℝ) • b i) := by
        rw [b.sum_repr]
        simp only [Int.cast_smul_eq_zsmul,y]
      _ = _ := by rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _; rw [sub_smul]
  refine ⟨y,hy,?_⟩
  rw [he]
  calc
    _ ≤ ∑ i, ‖(b.repr x i-(c i : ℝ)) • b i‖ := norm_sum_le _ _
    _ = ∑ i, |b.repr x i-(c i : ℝ)| *‖b i‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ∑ i, (ε i/4)*‖b i‖ :=
      sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _))
    _ = _ := by rw [sum_div]; apply sum_congr rfl; intro i _; ring

#print axioms exists_lattice_near_of_chords
#print axioms dualFrequency_integral
end Erdos3LatticePhaseCoordinates
