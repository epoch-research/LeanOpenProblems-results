import Submission.AlgClosedSpecialization

/-!
Tensor products of field extensions over an algebraically closed field.
This auxiliary algebra does not settle Erdős 595.
-/
set_option autoImplicit false
open scoped TensorProduct
open Module
namespace Erdos595AlgClosedTensorDomain

section Coefficients
variable {F A C D J : Type*} [Field F] [CommRing A] [Algebra F A]
  [CommRing C] [Algebra F C] [CommRing D] [Algebra F D] [DecidableEq J]
  (b : Basis J F A)

lemma coeff_map (g : C →ₐ[F] D) (x : A ⊗[F] C) (j : J) :
    TensorProduct.equivFinsuppOfBasisLeft b (Algebra.TensorProduct.map (AlgHom.id F A) g x) j =
      g (TensorProduct.equivFinsuppOfBasisLeft b x j) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [Algebra.TensorProduct.map_tmul,AlgHom.id_apply,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,map_smul]
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]

include b in
lemma map_right_injective (g : C →ₐ[F] D) (hg : Function.Injective g) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id F A) g) := by
  intro x y h
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext j
  apply hg
  rw [← coeff_map b,← coeff_map b,h]

lemma coord_rid (x : A ⊗[F] F) (j : J) :
    b.coord j (Algebra.TensorProduct.rid F F A x) =
      TensorProduct.equivFinsuppOfBasisLeft b x j := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [Algebra.TensorProduct.rid_tmul,map_smul,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    change c * b.repr a j = b.repr a j * c
    exact mul_comm _ _
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]

end Coefficients

section Restrict
variable {F K J : Type*} [Field F] [Field K] [Algebra F K]
  (C : Subalgebra F K) (d : J →₀ K) (hd : ∀ j, d j ∈ C)

noncomputable def restrictCoeffs : J →₀ C where
  toFun j := ⟨d j,hd j⟩
  support := d.support
  mem_support_toFun := by
    intro j
    simp only [Finsupp.mem_support_iff,ne_eq,Subtype.ext_iff]
    rfl

@[simp] lemma restrictCoeffs_apply (j : J) :
    (restrictCoeffs C d hd j : K) = d j := rfl

end Restrict

section Domain
variable (F A K : Type*) [Field F] [IsAlgClosed F] [Field A] [Field K]
  [Algebra F A] [Algebra F K]

/-- Specializing a finite coefficient algebra separates two nonzero tensors. -/
theorem mul_ne_zero (u v : A ⊗[F] K) (hu : u ≠ 0) (hv : v ≠ 0) : u * v ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis F A
  let d := TensorProduct.equivFinsuppOfBasisLeft b u
  let e := TensorProduct.equivFinsuppOfBasisLeft b v
  have hdi : ∃ i, d i ≠ 0 := by
    by_contra! hn
    apply hu
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext i
    simpa only [map_zero,Finsupp.zero_apply] using hn i
  have hej : ∃ j, e j ≠ 0 := by
    by_contra! hn
    apply hv
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext j
    simpa only [map_zero,Finsupp.zero_apply] using hn j
  obtain ⟨i,hi⟩ := hdi
  obtain ⟨j,hj⟩ := hej
  let T : Finset K := insert (d i)⁻¹ (insert (e j)⁻¹
    ((d.support.image d) ∪ (e.support.image e)))
  let C := Algebra.adjoin F (T : Set K)
  have hdC (k) : d k ∈ C := by
    by_cases hk : d k = 0
    · rw [hk]; exact C.zero_mem
    · exact Algebra.subset_adjoin (by
        simp only [T,Finset.mem_coe,Finset.mem_insert,Finset.mem_union]
        exact Or.inr (Or.inr (Or.inl (Finset.mem_image.mpr
          ⟨k,Finsupp.mem_support_iff.mpr hk,rfl⟩))))
  have heC (k) : e k ∈ C := by
    by_cases hk : e k = 0
    · rw [hk]; exact C.zero_mem
    · exact Algebra.subset_adjoin (by
        simp only [T,Finset.mem_coe,Finset.mem_insert,Finset.mem_union]
        exact Or.inr (Or.inr (Or.inr (Finset.mem_image.mpr
          ⟨k,Finsupp.mem_support_iff.mpr hk,rfl⟩))))
  have hdiC : (d i)⁻¹ ∈ C := Algebra.subset_adjoin (by simp [T])
  have hejC : (e j)⁻¹ ∈ C := Algebra.subset_adjoin (by simp [T])
  letI : Algebra.FiniteType F C := Algebra.FiniteType.adjoin_of_finite T.finite_toSet
  obtain ⟨ψ⟩ := Erdos595AlgClosedSpecialization.exists_hom F C
  let dC := restrictCoeffs C d hdC
  let eC := restrictCoeffs C e heC
  let uC := (TensorProduct.equivFinsuppOfBasisLeft b).symm dC
  let vC := (TensorProduct.equivFinsuppOfBasisLeft b).symm eC
  let inc := Algebra.TensorProduct.map (AlgHom.id F A) C.val
  have hinc : Function.Injective inc := map_right_injective b C.val Subtype.val_injective
  have huC : inc uC = u := by
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext k
    rw [coeff_map]
    simp only [uC,LinearEquiv.apply_symm_apply]
    rfl
  have hvC : inc vC = v := by
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext k
    rw [coeff_map]
    simp only [vC,LinearEquiv.apply_symm_apply]
    rfl
  let s : A ⊗[F] C →ₐ[F] A :=
    (Algebra.TensorProduct.rid F F A).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id F A) ψ)
  have hdu : IsUnit (dC i) := by
    apply IsUnit.of_mul_eq_one (⟨(d i)⁻¹,hdiC⟩ : C)
    apply Subtype.ext
    exact mul_inv_cancel₀ hi
  have hev : IsUnit (eC j) := by
    apply IsUnit.of_mul_eq_one (⟨(e j)⁻¹,hejC⟩ : C)
    apply Subtype.ext
    exact mul_inv_cancel₀ hj
  have hsu : s uC ≠ 0 := by
    intro hz
    have hc := congrArg (b.coord i) hz
    change b.coord i (Algebra.TensorProduct.rid F F A
      (Algebra.TensorProduct.map (AlgHom.id F A) ψ uC)) = b.coord i 0 at hc
    rw [coord_rid,coeff_map] at hc
    simp only [uC,LinearEquiv.apply_symm_apply,map_zero] at hc
    exact (hdu.map ψ).ne_zero hc
  have hsv : s vC ≠ 0 := by
    intro hz
    have hc := congrArg (b.coord j) hz
    change b.coord j (Algebra.TensorProduct.rid F F A
      (Algebra.TensorProduct.map (AlgHom.id F A) ψ vC)) = b.coord j 0 at hc
    rw [coord_rid,coeff_map] at hc
    simp only [vC,LinearEquiv.apply_symm_apply,map_zero] at hc
    exact (hev.map ψ).ne_zero hc
  intro huv
  have hzero : uC * vC = 0 := hinc (by rw [map_mul,huC,hvC,huv,map_zero])
  exact (_root_.mul_ne_zero hsu hsv) (by rw [← map_mul,hzero,map_zero])

/-- Tensor products of arbitrary field extensions of an algebraically closed
field have no zero divisors. -/
theorem tensor_noZeroDivisors : NoZeroDivisors (A ⊗[F] K) := by
  refine ⟨fun {u v} h => ?_⟩
  by_contra! hn
  exact mul_ne_zero F A K u v hn.1 hn.2 h

/-- The abstract tensor product is an integral domain. This alone does not
assert injectivity of its multiplication map into a chosen common overfield. -/
theorem tensor_isDomain : IsDomain (A ⊗[F] K) := by
  letI := tensor_noZeroDivisors F A K
  letI : Nontrivial (A ⊗[F] K) := Function.Injective.nontrivial
    (f := (Algebra.TensorProduct.includeLeft : A →ₐ[F] A ⊗[F] K))
    (Algebra.TensorProduct.includeLeft_injective (RingHom.injective (algebraMap F K)))
  exact NoZeroDivisors.to_isDomain _

end Domain

#print axioms tensor_isDomain
#print axioms mul_ne_zero
#print axioms coeff_map
#print axioms map_right_injective
end Erdos595AlgClosedTensorDomain
