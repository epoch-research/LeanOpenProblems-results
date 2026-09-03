import Submission.AlgClosedTensorDomain

/-!
Injectivity through algebraic extensions of a tensor factor. This is auxiliary
algebra, not a proof or disproof of Erdős 595.
-/
set_option autoImplicit false
open scoped TensorProduct
namespace Erdos595AlgClosedTensorInjection

section General
variable {D R L : Type*} [CommRing D]
  [CommRing R] [NoZeroDivisors R] [Ring L] [Algebra D R]
  [Algebra.IsAlgebraic D R]

theorem injective_of_algebraic_comp (f : R →+* L)
    (hf : Function.Injective (f.comp (algebraMap D R))) : Function.Injective f := by
  apply (injective_iff_map_eq_zero f).mpr
  intro x hx
  by_contra hn
  obtain ⟨d,hd,y,hy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := D) x).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hn)
  apply hd
  apply hf
  change f (algebraMap D R d) = f (algebraMap D R 0)
  rw [hy,map_mul,hx,zero_mul,map_zero,map_zero]

end General

section TensorExtension
variable (F C B A : Type*) [Field F] [CommRing C] [CommRing B] [CommRing A]
  [Algebra F C] [Algebra F B] [Algebra F A]
  [Algebra C B] [IsScalarTower F C B]

noncomputable def extension : C ⊗[F] A →ₐ[F] B ⊗[F] A :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom F C B) (AlgHom.id F A)

@[simp] lemma extension_tmul (c : C) (a : A) :
    extension F C B A (c ⊗ₜ[F] a) = algebraMap C B c ⊗ₜ[F] a := rfl

/-- Integrality is preserved on changing the other tensor factor. -/
theorem integral_extension [Algebra.IsIntegral C B] :
    letI : Algebra (C ⊗[F] A) (B ⊗[F] A) := (extension F C B A).toRingHom.toAlgebra
    Algebra.IsIntegral (C ⊗[F] A) (B ⊗[F] A) := by
  letI : Algebra (C ⊗[F] A) (B ⊗[F] A) := (extension F C B A).toRingHom.toAlgebra
  refine ⟨fun x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => exact isIntegral_zero
  | tmul b a =>
    have hb : IsIntegral (C ⊗[F] A) (b ⊗ₜ[F] (1 : A)) := by
      apply IsIntegral.map_of_comp_eq (algebraMap C (C ⊗[F] A))
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[F] A) _
        (Algebra.IsIntegral.isIntegral b)
      ext c
      rfl
    have ha : IsIntegral (C ⊗[F] A) ((1 : B) ⊗ₜ[F] a) := by
      have h := isIntegral_algebraMap (R := C ⊗[F] A) (A := B ⊗[F] A)
        (x := (1 : C) ⊗ₜ[F] a)
      change IsIntegral (C ⊗[F] A) (extension F C B A ((1 : C) ⊗ₜ[F] a)) at h
      simpa only [extension_tmul,map_one] using h
    simpa only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul] using hb.mul ha
  | add x y hx hy => exact hx.add hy

/-- The analogous base-change result for algebraicity needs the tensor base
ring to be a domain. -/
theorem algebraic_extension [Algebra.IsAlgebraic C B] [Nontrivial A]
    [IsDomain (C ⊗[F] A)] :
    letI : Algebra (C ⊗[F] A) (B ⊗[F] A) := (extension F C B A).toRingHom.toAlgebra
    Algebra.IsAlgebraic (C ⊗[F] A) (B ⊗[F] A) := by
  letI : Algebra (C ⊗[F] A) (B ⊗[F] A) := (extension F C B A).toRingHom.toAlgebra
  refine ⟨fun x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => exact isAlgebraic_zero
  | tmul b a =>
    have hb : IsAlgebraic (C ⊗[F] A) (b ⊗ₜ[F] (1 : A)) := by
      apply (Algebra.IsAlgebraic.isAlgebraic (R := C) b).ringHom_of_comp_eq
        (algebraMap C (C ⊗[F] A))
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[F] A)
      · exact Algebra.TensorProduct.includeLeft_injective (R := F) (S := C) (A := C) (B := A) (RingHom.injective (algebraMap F A))
      · ext c
        simp only [RingHom.comp_apply,Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self,RingHom.id_apply,RingHom.algebraMap_toAlgebra,
          AlgHom.toRingHom_eq_coe,Algebra.TensorProduct.includeLeftRingHom_apply]
        rfl
    have ha : IsAlgebraic (C ⊗[F] A) ((1 : B) ⊗ₜ[F] a) := by
      have h := isAlgebraic_algebraMap (R := C ⊗[F] A) (A := B ⊗[F] A)
        ((1 : C) ⊗ₜ[F] a)
      change IsAlgebraic (C ⊗[F] A) (extension F C B A ((1 : C) ⊗ₜ[F] a)) at h
      simpa only [extension_tmul,map_one] using h
    simpa only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul] using hb.mul ha
  | add x y hx hy => exact hx.add hy

end TensorExtension

section FieldExtension
variable (F C B A L : Type*) [Field F] [IsAlgClosed F]
  [Field C] [Field B] [Field A] [Ring L]
  [Algebra F C] [Algebra F B] [Algebra F A]
  [Algebra C B] [IsScalarTower F C B] [Algebra.IsAlgebraic C B]

/-- If a multiplication map is injective before an algebraic extension of one
factor, it remains injective afterwards, over an algebraically closed base. -/
theorem injective_extension (f : B ⊗[F] A →+* L)
    (hf : Function.Injective (f.comp (extension F C B A).toRingHom)) :
    Function.Injective f := by
  letI := Erdos595AlgClosedTensorDomain.tensor_isDomain F C A
  letI := Erdos595AlgClosedTensorDomain.tensor_isDomain F B A
  letI : Algebra (C ⊗[F] A) (B ⊗[F] A) := (extension F C B A).toRingHom.toAlgebra
  letI : Algebra.IsIntegral (C ⊗[F] A) (B ⊗[F] A) := integral_extension F C B A
  letI : Algebra.IsAlgebraic (C ⊗[F] A) (B ⊗[F] A) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  exact injective_of_algebraic_comp f hf

end FieldExtension

section DomainBase
variable (F C B A L : Type*) [Field F] [IsAlgClosed F]
  [CommRing C] [Field B] [Field A] [CommRing L] [IsDomain L]
  [Algebra F C] [Algebra F B] [Algebra F A]
  [Algebra C B] [IsScalarTower F C B] [Algebra.IsAlgebraic C B]

/-- The smaller factor may be a ring (for instance a polynomial ring). -/
theorem injective_extension_of_domain (f : B ⊗[F] A →+* L)
    (hf : Function.Injective (f.comp (extension F C B A).toRingHom)) :
    Function.Injective f := by
  let j := f.comp (extension F C B A).toRingHom
  letI : IsDomain (C ⊗[F] A) := Function.Injective.isDomain j hf
  letI := Erdos595AlgClosedTensorDomain.tensor_isDomain F B A
  letI : Algebra (C ⊗[F] A) (B ⊗[F] A) := (extension F C B A).toRingHom.toAlgebra
  letI : Algebra.IsAlgebraic (C ⊗[F] A) (B ⊗[F] A) := algebraic_extension F C B A
  exact injective_of_algebraic_comp f hf

end DomainBase

#print axioms integral_extension
#print axioms injective_extension
#print axioms injective_extension_of_domain
end Erdos595AlgClosedTensorInjection
