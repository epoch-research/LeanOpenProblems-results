import Submission.CountableFieldUniversal
import Submission.AlgebraicBilinearTransfer

/-!
Countable common-root specialization fields for finite supports. This file
is auxiliary to an algebraic graph-covering theorem.
-/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
open Set
open scoped TensorProduct BigOperators
namespace Erdos595AlgebraicRootSpecialization
open Erdos595AlgebraicSupportFields Erdos595CountableFieldUniversal

variable (F : Type*) {L I : Type*} [Field F] [Field L] [Algebra F L]
  (t : I → L)

abbrev Root (R : Finset I) : IntermediateField F L := closure F (t '' (R : Set I))

abbrev Outside (R : Finset I) := {i : I // i ∉ R}

def privateSet (R S : Finset I) : Set (Outside R) := {i | i.val ∈ S}

def privateGenerators (R : Finset I) : Outside R → L := fun i => t i.val

abbrev Local (R S : Finset I) : IntermediateField (Root F t R) L :=
  closure (Root F t R) (privateGenerators t R '' privateSet R S)

instance root_countable [Countable F] (R : Finset I) : Countable (Root F t R) :=
  countable_closure F _ (R.finite_toSet.image t).countable

lemma privateSet_finite (R S : Finset I) : (privateSet R S).Finite :=
  S.finite_toSet.preimage Subtype.val_injective.injOn

instance local_countable [Countable F] (R S : Finset I) : Countable (Local F t R S) :=
  countable_closure (Root F t R) _ ((privateSet_finite R S).image (privateGenerators t R)).countable

/-- Every supported element lies in its rebased local field, even when the
chosen root is not a subset of its support. -/
theorem local_contains [IsAlgClosed L] (R S : Finset I) :
    closure F (t '' (S : Set I)) ≤ (Local F t R S).restrictScalars F := by
  rw [closure_rebase]
  apply closure_mono F
  rintro _ ⟨i,hi,rfl⟩
  by_cases hir : i ∈ R
  · exact Or.inl (mem_image_of_mem t hir)
  · exact Or.inr ⟨⟨i,hir⟩,hi,rfl⟩

/-- Distinct private supports are independent over the common root. -/
theorem local_mul_injective [IsAlgClosed L] (ht : AlgebraicIndependent F t)
    (R S T : Finset I) (hST : ∀ i, i ∈ S → i ∈ T → i ∈ R) :
    Function.Injective (Erdos595AlgClosedLinearDisjoint.mulHom
      (Root F t R) (Local F t R S) (Local F t R T) L) := by
  have h : AlgebraicIndependent (Root F t R) (privateGenerators t R) :=
    independent_over_closure ht disjoint_compl_right
  apply disjoint_mul_injective h
  rw [Set.disjoint_left]
  intro i hi hj
  exact i.property (hST i.val hi hj)

noncomputable def embed [Countable F] (R S : Finset I) :
    Local F t R S →ₐ[Root F t R] Omega (Root F t R) :=
  Classical.choice (exists_hom (Root F t R) (Local F t R S))

#print axioms local_contains
#print axioms local_mul_injective
#print axioms embed
end Erdos595AlgebraicRootSpecialization
