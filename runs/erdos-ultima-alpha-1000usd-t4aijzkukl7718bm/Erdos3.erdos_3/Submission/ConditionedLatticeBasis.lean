import Submission.ReducedLatticeBasis

/-! Dual coordinate conditioning from the product bound for a reduced lattice
basis. Hadamard's inequality is applied after replacing one basis vector by
the normalized Riesz representative of its coordinate functional. -/
namespace Erdos3ConditionedLatticeBasis
open Finset Module MeasureTheory Erdos3LatticePhaseCoordinates
  Erdos3NormalOrthonormalBasis Erdos3PrimitiveKernelCovolume Erdos3ReducedLatticeBasis
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma determinant_update_coordinate (o b : Basis I ℝ E) (x : E) (i : I) :
    o.det (Function.update b i x) = (b.repr x i)*o.det b := by
  conv_lhs => rw [← b.sum_repr x]
  rw [o.det.map_update_sum]
  simp_rw [o.det.map_update_smul,smul_eq_mul]
  rw [sum_eq_single i]
  · rw [Function.update_eq_self]
  · intro j _ hji
    rw [o.det.map_update_self b hji.symm,mul_zero]
  · simp

lemma orthonormal_det_le_product {n : ℕ} (o : OrthonormalBasis (Fin n) ℝ E) (x : Fin n → E) :
    |o.toBasis.det x| ≤ ∏ i, ‖x i‖ := by
  letI : Fact (finrank ℝ E = n) := ⟨by simpa using finrank_eq_card_basis o.toBasis⟩
  have hh := o.toBasis.orientation.abs_volumeForm_apply_le x
  rwa [o.toBasis.orientation.volumeForm_robust' o x] at hh

lemma coordinate_conditioning_product {n : ℕ} (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) (i : Fin n) :
    ‖b i‖*‖coordinate b i‖*|o.toBasis.det b| ≤ ∏ j, ‖b j‖ := by
  let F := coordinate b i
  have hFi : F (b i) = 1 := by simp [F,coordinate_basis]
  have hF : F ≠ 0 := by intro hz; simp [hz] at hFi
  let u := unitNormal F
  have hu : ‖u‖ = 1 := unitNormal_norm F hF
  have hcoord : b.repr u i = ‖F‖ := unitNormal_evaluate F hF
  have hdet : |o.toBasis.det (Function.update b i u)| = ‖F‖*|o.toBasis.det b| := by
    rw [determinant_update_coordinate,hcoord,abs_mul,abs_of_nonneg (norm_nonneg _)]
  have hprod : (∏ j, ‖Function.update b i u j‖) = ∏ j ∈ univ.erase i, ‖b j‖ := by
    have he : (fun j ↦ ‖Function.update b i u j‖) = Function.update (fun j ↦ ‖b j‖) i 1 := by
      funext j
      by_cases hj : j = i
      · subst j; simp [hu]
      · simp [Function.update_of_ne hj]
    rw [he,prod_update_of_mem (mem_univ i),one_mul,sdiff_singleton_eq_erase]
  have hbound := orthonormal_det_le_product o (Function.update b i u)
  rw [hdet,hprod] at hbound
  calc
    _ = ‖b i‖*(‖F‖*|o.toBasis.det b|) := by dsimp only [F]; ring
    _ ≤ ‖b i‖*(∏ j ∈ univ.erase i, ‖b j‖) :=
      mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = _ := mul_prod_erase univ (fun j ↦ ‖b j‖) (mem_univ i)

variable [MeasurableSpace E] [BorelSpace E]

lemma lattice_coordinate_conditioning {n : ℕ} (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis (Fin n) ℤ L)
    (C : ℝ) (hprod : (∏ i, ‖(b i : E)‖) ≤ C*ZLattice.covolume L) (i : Fin n) :
    ‖(b i : E)‖*‖coordinate (b.ofZLatticeBasis ℝ) i‖ ≤ C := by
  have hdim : finrank ℝ E = n := by simpa using finrank_eq_card_basis (b.ofZLatticeBasis ℝ)
  let e : Fin (finrank ℝ E) ≃ Fin n := Fintype.equivOfCardEq (by simp [hdim])
  let o := (stdOrthonormalBasis ℝ E).reindex e
  have hbound := coordinate_conditioning_product o (b.ofZLatticeBasis ℝ) i
  simp only [Basis.ofZLatticeBasis_apply] at hbound
  have hco : (b.ofZLatticeBasis ℝ : Fin n → E) = (fun j ↦ (b j : E)) :=
    funext (fun j ↦ Basis.ofZLatticeBasis_apply ℝ L b j)
  rw [hco,← covolume_eq_orthonormal_det L b o] at hbound
  have hh := hbound.trans hprod
  exact (mul_le_mul_iff_left₀ (ZLattice.covolume_pos L)).mp hh

/-- A full Euclidean lattice admits a basis with both a product bound and a
uniform bound on norm(b_i) times the norm of its dual coordinate functional. -/
theorem exists_conditioned_lattice_basis (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ E,
      Submodule.span ℤ (Set.range b) = L ∧
      (∏ i, ‖b i‖) ≤ (2:ℝ)^((finrank ℝ E)^2)*ZLattice.covolume L ∧
      ∀ i, ‖b i‖*‖coordinate b i‖ ≤ (2:ℝ)^((finrank ℝ E)^2) := by
  obtain ⟨b,hb⟩ := exists_reduced_lattice_basis L
  refine ⟨b.ofZLatticeBasis ℝ,b.ofZLatticeBasis_span ℝ,?_,?_⟩
  · simpa only [Basis.ofZLatticeBasis_apply] using hb
  · intro i
    simpa only [Basis.ofZLatticeBasis_apply] using lattice_coordinate_conditioning L b _ hb i

#print axioms exists_conditioned_lattice_basis
end Erdos3ConditionedLatticeBasis
