import Submission.AlgClosedLinearDisjoint
import Submission.PolynomialOrthogonalityCover

/-! Bilinear equations transfer across independently embedded tensor factors. -/
set_option autoImplicit false
open scoped TensorProduct BigOperators
namespace Erdos595AlgebraicBilinearTransfer
open Erdos595PolynomialOrthogonality Erdos595AlgClosedLinearDisjoint

variable {F U V L W J : Type*} [Field F] [Field U] [Field V] [CommRing L] [CommRing W]
  [Algebra F U] [Algebra F V] [Algebra F L] [Algebra F W]
  [Algebra U L] [Algebra V L] [IsScalarTower F U L] [IsScalarTower F V L]
  [Fintype J]

theorem form_zero_of_injective
    (hm : Function.Injective (mulHom F U V L))
    (f : U →ₐ[F] W) (g : V →ₐ[F] W) (B : J → J → F)
    (x : J → U) (y : J → V)
    (h : form B (algebraMap F L) (fun i => algebraMap U L (x i))
      (fun j => algebraMap V L (y j)) = 0) :
    form B (algebraMap F W) (fun i => f (x i)) (fun j => g (y j)) = 0 := by
  classical
  let z : U ⊗[F] V := ∑ i, ∑ j, (algebraMap F U (B i j) * x i) ⊗ₜ[F] y j
  have hz : z = 0 := hm (by
    simpa only [z,map_sum,mulHom_tmul,map_mul,← IsScalarTower.algebraMap_apply,
      map_zero,form] using h)
  let n : U ⊗[F] V →ₐ[F] W := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have hn := congrArg n hz
  simpa only [z,map_sum,n,Algebra.TensorProduct.lift_tmul,map_mul,
    AlgHom.commutes,map_zero,form] using hn

/-- A nonzero diagonal value remains nonzero under a field embedding. -/
theorem form_nonzero_of_embedding [Nontrivial W]
    (f : U →ₐ[F] W) (B : J → J → F) (x : J → U)
    (h : form B (algebraMap F L) (fun i => algebraMap U L (x i))
      (fun j => algebraMap U L (x j)) ≠ 0) :
    form B (algebraMap F W) (fun i => f (x i)) (fun j => f (x j)) ≠ 0 := by
  intro he
  have hz : form B (algebraMap F U) x x = 0 := by
    apply (show Function.Injective f from f.injective)
    simpa only [form,map_sum,map_mul,AlgHom.commutes,map_zero] using he
  have hh := congrArg (algebraMap U L) hz
  apply h
  simpa only [form,map_sum,map_mul,← IsScalarTower.algebraMap_apply,map_zero] using hh

/-- Change the coefficient field along a scalar tower. -/
lemma form_tower (B : J → J → F) (x y : J → L) :
    form (fun i j => algebraMap F U (B i j)) (algebraMap U L) x y =
      form B (algebraMap F L) x y := by
  simp only [form,← IsScalarTower.algebraMap_apply]

#print axioms form_nonzero_of_embedding
#print axioms form_zero_of_injective
end Erdos595AlgebraicBilinearTransfer
