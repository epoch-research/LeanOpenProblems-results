import FormalConjecturesUtil

/-!
Finite-type specializations over an algebraically closed field. These are
algebraic auxiliaries for the orthogonality investigation, not a settlement
of Erdős 595.
-/
set_option autoImplicit false
open scoped TensorProduct
namespace Erdos595AlgClosedSpecialization

variable (F C : Type*) [Field F] [IsAlgClosed F]
  [CommRing C] [Nontrivial C] [Algebra F C] [Algebra.FiniteType F C]

/-- Weak Nullstellensatz in the form of an algebra-valued point. -/
theorem exists_hom : Nonempty (C →ₐ[F] F) := by
  classical
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  letI := Ideal.Quotient.field m
  letI := finite_of_finite_type_of_isJacobsonRing F (C ⧸ m)
  let e : F ≃ₐ[F] C ⧸ m := AlgEquiv.ofBijective (Algebra.ofId F (C ⧸ m))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ F m)⟩

#print axioms exists_hom
end Erdos595AlgClosedSpecialization
