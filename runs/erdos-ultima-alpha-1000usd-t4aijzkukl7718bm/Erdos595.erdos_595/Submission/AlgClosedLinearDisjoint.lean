import Submission.AlgClosedTensorInjection

/-!
Actual tensor multiplication is injective when a transcendence basis of one
factor remains algebraically independent over the other factor. This is an
auxiliary field-theoretic result, not a solution of Erdős 595.
-/
set_option autoImplicit false
open scoped TensorProduct
namespace Erdos595AlgClosedLinearDisjoint
open Erdos595AlgClosedTensorInjection

section Polynomial
variable (F A L : Type*) {I : Type*} [CommRing F] [CommRing A] [CommRing L]
  [Algebra F A] [Algebra F L] [Algebra A L] [IsScalarTower F A L]

noncomputable def polyHom (t : I → L) : MvPolynomial I F ⊗[F] A →ₐ[F] L :=
  Algebra.TensorProduct.lift (MvPolynomial.aeval t) (IsScalarTower.toAlgHom F A L)
    (fun _ _ => Commute.all _ _)

@[simp] theorem polyHom_tmul (t : I → L) (p : MvPolynomial I F) (a : A) :
    polyHom F A L t (p ⊗ₜ[F] a) = MvPolynomial.aeval t p * algebraMap A L a := rfl

/-- Polynomial tensor multiplication is injective precisely where algebraic
independence supplies the required polynomial evaluation injectivity. -/
theorem poly_tensor_injective (t : I → L) (ht : AlgebraicIndependent A t) :
    Function.Injective (polyHom F A L t) := by
  let e : MvPolynomial I F ⊗[F] A ≃ₐ[F] MvPolynomial I A :=
    (Algebra.TensorProduct.comm F _ _).trans
      ((MvPolynomial.algebraTensorAlgEquiv F A).restrictScalars F)
  have he : polyHom F A L t =
      ((MvPolynomial.aeval t : MvPolynomial I A →ₐ[A] L).restrictScalars F).comp e.toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro p a
    simp only [polyHom_tmul,AlgHom.comp_apply,AlgHom.coe_restrictScalars',
      AlgEquiv.coe_algHom,e,AlgEquiv.trans_apply,AlgEquiv.coe_restrictScalars',
      Algebra.TensorProduct.comm_tmul,MvPolynomial.algebraTensorAlgEquiv_tmul,
      Algebra.smul_def,map_mul,AlgHom.commutes,MvPolynomial.aeval_map_algebraMap,mul_comm]
  rw [he]
  exact (algebraicIndependent_iff_injective_aeval.mp ht).comp e.injective

end Polynomial

section Multiplication
variable (F B A L : Type*) [CommRing F] [CommRing B] [CommRing A] [CommRing L]
  [Algebra F B] [Algebra F A] [Algebra F L]
  [Algebra B L] [Algebra A L] [IsScalarTower F B L] [IsScalarTower F A L]

noncomputable def mulHom : B ⊗[F] A →ₐ[F] L :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom F B L) (IsScalarTower.toAlgHom F A L)
    (fun _ _ => Commute.all _ _)

@[simp] theorem mulHom_tmul (b : B) (a : A) :
    mulHom F B A L (b ⊗ₜ[F] a) = algebraMap B L b * algebraMap A L a := rfl

end Multiplication

section PolynomialAlgebra
variable (F B A L : Type*) (I : Type*) [Field F] [IsAlgClosed F]
  [Field B] [Field A] [Field L]
  [Algebra F B] [Algebra F A] [Algebra F L]
  [Algebra B L] [Algebra A L] [IsScalarTower F B L] [IsScalarTower F A L]
  [Algebra (MvPolynomial I F) B] [IsScalarTower F (MvPolynomial I F) B]
  [Algebra.IsAlgebraic (MvPolynomial I F) B]

/-- The polynomial-algebra formulation avoids any fraction-ring localization. -/
theorem injective_of_polynomial_algebra
    (ht : AlgebraicIndependent A (fun i : I =>
      algebraMap B L (algebraMap (MvPolynomial I F) B (MvPolynomial.X i)))) :
    Function.Injective (mulHom F B A L) := by
  apply injective_extension_of_domain F (MvPolynomial I F) B A L (mulHom F B A L).toRingHom
  let t : I → L := fun i => algebraMap B L (algebraMap (MvPolynomial I F) B (MvPolynomial.X i))
  have hp : (IsScalarTower.toAlgHom F B L).comp
      (IsScalarTower.toAlgHom F (MvPolynomial I F) B) = MvPolynomial.aeval t := by
    ext i
    simp only [AlgHom.comp_apply,IsScalarTower.coe_toAlgHom',MvPolynomial.aeval_X,t]
  have he : (mulHom F B A L).comp (extension F (MvPolynomial I F) B A) = polyHom F A L t := by
    apply Algebra.TensorProduct.ext'
    intro p a
    rw [AlgHom.comp_apply,extension_tmul,mulHom_tmul,polyHom_tmul]
    exact congrArg (fun x => x * algebraMap A L a) (DFunLike.congr_fun hp p)
  change Function.Injective ((mulHom F B A L).comp (extension F (MvPolynomial I F) B A))
  rw [he]
  exact poly_tensor_injective F A L t ht

end PolynomialAlgebra

section TranscendenceBasis
variable (F B A L : Type*) {I : Type*} [Field F] [IsAlgClosed F]
  [Field B] [Field A] [Field L]
  [Algebra F B] [Algebra F A] [Algebra F L]
  [Algebra B L] [Algebra A L] [IsScalarTower F B L] [IsScalarTower F A L]

/-- A transcendence basis which stays independent over the other factor
suffices for injectivity of the actual multiplication map. -/
theorem injective_of_transcendenceBasis (t : I → B)
    (ht : IsTranscendenceBasis F t)
    (hA : AlgebraicIndependent A (fun i => algebraMap B L (t i))) :
    Function.Injective (mulHom F B A L) := by
  let P := MvPolynomial I F
  letI : Algebra P B := (MvPolynomial.aeval t : P →ₐ[F] B).toRingHom.toAlgebra
  letI : IsScalarTower F P B := IsScalarTower.of_algebraMap_eq fun r =>
    ((MvPolynomial.aeval t : P →ₐ[F] B).commutes r).symm
  let C := Algebra.adjoin F (Set.range t)
  let e : P ≃ₐ[F] C := ht.1.aevalEquiv
  letI : Algebra.IsAlgebraic C B := ht.isAlgebraic
  letI : Algebra.IsAlgebraic P B :=
    Algebra.IsAlgebraic.of_ringHom_of_comp_eq e (RingHom.id B) e.surjective
      Function.injective_id (by
        apply RingHom.ext
        intro p
        exact ht.1.algebraMap_aevalEquiv p)
  apply injective_of_polynomial_algebra F B A L I
  change AlgebraicIndependent A (fun i => algebraMap B L
    ((MvPolynomial.aeval t : P →ₐ[F] B) (MvPolynomial.X i)))
  simpa only [MvPolynomial.aeval_X] using hA

/-- A version with algebraicity stated in the common overfield. This is useful
for relative algebraic closures of prescribed sets of generators. -/
theorem injective_of_algebraic_generators (t : I → B)
    (ht : AlgebraicIndependent F (fun i => algebraMap B L (t i)))
    (halg : ∀ b : B, IsAlgebraic
      (Algebra.adjoin F (Set.range (fun i => algebraMap B L (t i)))) (algebraMap B L b))
    (hA : AlgebraicIndependent A (fun i => algebraMap B L (t i))) :
    Function.Injective (mulHom F B A L) := by
  let P := MvPolynomial I F
  letI : Algebra P B := (MvPolynomial.aeval t : P →ₐ[F] B).toRingHom.toAlgebra
  letI : IsScalarTower F P B := IsScalarTower.of_algebraMap_eq fun r =>
    ((MvPolynomial.aeval t : P →ₐ[F] B).commutes r).symm
  let C := Algebra.adjoin F (Set.range (fun i => algebraMap B L (t i)))
  let e : P ≃ₐ[F] C := ht.aevalEquiv
  have hev : (IsScalarTower.toAlgHom F B L).comp (MvPolynomial.aeval t) =
      MvPolynomial.aeval (fun i => algebraMap B L (t i)) := by
    ext i
    simp only [AlgHom.comp_apply,MvPolynomial.aeval_X,IsScalarTower.coe_toAlgHom']
  letI : Algebra.IsAlgebraic P B := ⟨fun b =>
    (halg b).of_ringHom_of_comp_eq e (algebraMap B L) e.surjective
      (RingHom.injective _) (by
        apply RingHom.ext
        intro p
        exact (ht.algebraMap_aevalEquiv p).trans (DFunLike.congr_fun hev p).symm)⟩
  apply injective_of_polynomial_algebra F B A L I
  change AlgebraicIndependent A (fun i => algebraMap B L
    ((MvPolynomial.aeval t : P →ₐ[F] B) (MvPolynomial.X i)))
  simpa only [MvPolynomial.aeval_X] using hA

end TranscendenceBasis

section IntermediateFields
variable {F L : Type*} [Field F] [IsAlgClosed F] [Field L] [Algebra F L]

/-- The equivalent statement in Mathlib's linear-disjointness vocabulary. -/
theorem linearDisjoint_of_transcendenceBasis (B A : IntermediateField F L)
    {I : Type*} (t : I → B) (ht : IsTranscendenceBasis F t)
    (hA : AlgebraicIndependent A (fun i => (t i : L))) : B.LinearDisjoint A := by
  rw [IntermediateField.linearDisjoint_iff',Subalgebra.linearDisjoint_iff_injective]
  exact injective_of_transcendenceBasis F B A L t ht hA

end IntermediateFields

#print axioms poly_tensor_injective
#print axioms injective_of_polynomial_algebra
#print axioms injective_of_transcendenceBasis
#print axioms injective_of_algebraic_generators
#print axioms linearDisjoint_of_transcendenceBasis
end Erdos595AlgClosedLinearDisjoint
