import Submission.OddFieldExtensionExplore

/-! A square-closed coordinate subspace in odd characteristic is not an
arbitrary vector-space prefix: in a finite field it is an intermediate field. -/
namespace Erdos66SquareClosedSubspace
open scoped Classical
set_option maxHeartbeats 1500000

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

lemma mul_mem_of_square_closed (V : Submodule F K) (h2 : (2:F)≠0)
    (hsq : ∀ x∈V, x^2∈V) {x y : K} (hx : x∈V) (hy : y∈V) : x*y∈V := by
  have hh := V.smul_mem ((2:F)⁻¹)
    (V.sub_mem (V.sub_mem (hsq (x+y) (V.add_mem hx hy)) (hsq x hx)) (hsq y hy))
  have h2K : (2:K)≠0 := by
    have hh := (map_ne_zero (algebraMap F K)).mpr h2
    simpa only [map_ofNat] using hh
  have he : ((2:F)⁻¹) • ((x+y)^2-x^2-y^2)=x*y := by
    rw [Algebra.smul_def,map_inv₀,map_ofNat]
    field_simp
    <;> ring
  rwa [he] at hh

noncomputable def squareClosedAlgebra (V : Submodule F K) (h1 : (1:K)∈V)
    (h2 : (2:F)≠0) (hsq : ∀ x∈V, x^2∈V) : Subalgebra F K where
  carrier := V
  zero_mem' := V.zero_mem
  one_mem' := h1
  add_mem' := V.add_mem
  mul_mem' := mul_mem_of_square_closed V h2 hsq
  algebraMap_mem' := fun a ↦ by
    have hh := V.smul_mem a h1
    simpa only [Algebra.smul_def,mul_one] using hh

@[simp] lemma mem_squareClosedAlgebra (V : Submodule F K) (h1 : (1:K)∈V)
    (h2 : (2:F)≠0) (hsq : ∀ x∈V, x^2∈V) (x : K) :
    x∈squareClosedAlgebra V h1 h2 hsq ↔ x∈V := Iff.rfl

variable [Algebra.IsAlgebraic F K]

noncomputable def squareClosedField (V : Submodule F K) (h1 : (1:K)∈V)
    (h2 : (2:F)≠0) (hsq : ∀ x∈V, x^2∈V) : IntermediateField F K :=
  Subalgebra.IsAlgebraic.toIntermediateField
    (S := squareClosedAlgebra V h1 h2 hsq) (fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x)

@[simp] lemma mem_squareClosedField (V : Submodule F K) (h1 : (1:K)∈V)
    (h2 : (2:F)≠0) (hsq : ∀ x∈V, x^2∈V) (x : K) :
    x∈squareClosedField V h1 h2 hsq ↔ x∈V := Iff.rfl

/-- Such a coordinate space is exactly an intermediate field, even in an
algebraic extension which is not assumed finite. -/
theorem square_closed_is_intermediate_field (V : Submodule F K) (h1 : (1:K)∈V)
    (h2 : (2:F)≠0) (hsq : ∀ x∈V, x^2∈V) :
    ∃ E : IntermediateField F K, (E:Set K)=(V:Set K) :=
  ⟨squareClosedField V h1 h2 hsq,rfl⟩

/-- A full square-graph coordinate prefix therefore has a divisibility
constraint on its dimension, not arbitrary intermediate dimensions. -/
theorem square_closed_finrank_dvd [FiniteDimensional F K]
    (V : Submodule F K) (h1 : (1:K)∈V)
    (h2 : (2:F)≠0) (hsq : ∀ x∈V, x^2∈V) :
    Module.finrank F V ∣ Module.finrank F K := by
  let E := squareClosedField V h1 h2 hsq
  refine ⟨Module.finrank E K,?_⟩
  change Module.finrank F K=Module.finrank F E*Module.finrank E K
  exact (Module.finrank_mul_finrank F E K).symm

end Erdos66SquareClosedSubspace
