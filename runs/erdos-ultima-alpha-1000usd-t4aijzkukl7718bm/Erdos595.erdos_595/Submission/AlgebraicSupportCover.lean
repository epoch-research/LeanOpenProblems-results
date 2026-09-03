import Submission.AlgebraicRootSpecialization

/-!
Countable triangle-free edge covers for nonisotropic finite-dimensional
bilinear representations supported on an independent family over a countable
coefficient field. This is a candidate exclusion, not a universal graph
representation theorem and not a solution of Erdős 595.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open Set SimpleGraph
open scoped TensorProduct BigOperators
namespace Erdos595AlgebraicSupportCover
open Erdos595Work Erdos595PolynomialOrthogonality Erdos595AlgebraicSupportFields
open Erdos595AlgebraicRootSpecialization Erdos595CountableFieldUniversal
open Erdos595AlgebraicBilinearTransfer

variable {F L I J V : Type*} [Field F] [Countable F] [Field L] [IsAlgClosed L]
  [Algebra F L] [Fintype J]
  (t : I → L) (B : J → J → F) (r : V → J → L) (s : V → Finset I)
  (hs : ∀ v j, r v j ∈ closure F (t '' (s v : Set I)))

noncomputable def localVector (R : Finset I) (v : V) : J → Local F t R (s v) :=
  fun j => ⟨r v j,local_contains F t R (s v) (hs v j)⟩

noncomputable def sample (R : Finset I) (v : V) : J → Omega (Root F t R) :=
  fun j => embed F t R (s v) (localVector t r s hs R v j)

/-- Isotropic vectors are isolated; this lets the target carrier be all tuples. -/
def target (R : Finset I) : SimpleGraph (J → Omega (Root F t R)) where
  Adj x y := form B (algebraMap F _) x y = 0 ∧ form B (algebraMap F _) y x = 0 ∧
    form B (algebraMap F _) x x ≠ 0 ∧ form B (algebraMap F _) y y ≠ 0
  symm := fun _ _ h => ⟨h.2.1,h.1,h.2.2.2,h.2.2.1⟩
  loopless := fun _ h => h.2.2.1 h.1

lemma sample_nonzero (R : Finset I) (v : V)
    (hv : form B (algebraMap F L) (r v) (r v) ≠ 0) :
    form B (algebraMap F _) (sample t r s hs R v) (sample t r s hs R v) ≠ 0 := by
  let C : J → J → Root F t R := fun i j => algebraMap F (Root F t R) (B i j)
  have h := form_nonzero_of_embedding (L := L) (embed F t R (s v)) C
    (localVector t r s hs R v) (by
      simpa only [C,form_tower] using hv)
  simpa only [C,form_tower] using h

lemma sample_zero (ht : AlgebraicIndependent F t) (R : Finset I) (v w : V)
    (hvw : ∀ i, i ∈ s v → i ∈ s w → i ∈ R)
    (he : form B (algebraMap F L) (r v) (r w) = 0) :
    form B (algebraMap F _) (sample t r s hs R v) (sample t r s hs R w) = 0 := by
  let C : J → J → Root F t R := fun i j => algebraMap F (Root F t R) (B i j)
  have h := form_zero_of_injective (local_mul_injective F t ht R (s v) (s w) hvw)
    (embed F t R (s v)) (embed F t R (s w)) C
    (localVector t r s hs R v) (localVector t r s hs R w) (by
      simpa only [C,form_tower] using he)
  simpa only [C,form_tower] using h

include hs in
/-- All cardinalities of the vertex and transcendence-generator types are
allowed. Only the coefficient field and each support are countable/finite. -/
theorem cover (ht : AlgebraicIndependent F t) (G : SimpleGraph V)
    (hr : ∀ v, form B (algebraMap F L) (r v) (r v) ≠ 0)
    (he : ∀ v w, G.Adj v w → form B (algebraMap F L) (r v) (r w) = 0) :
    IsCountableUnionOfTriangleFree G := by
  classical
  apply Erdos595PointCountableEdgeCover.finite_intersection_reduction G s
    (fun R => J → Omega (Root F t R)) (target t B) (sample t r s hs)
  · intro R
    exact countable_union_of_countable_common_neighbors _ (fun _ _ _ => Set.to_countable _)
  · intro v w hvw
    refine ⟨sample_zero t B r s hs ht _ v w (fun i hi hj => Finset.mem_inter.mpr ⟨hi,hj⟩)
      (he v w hvw),?_,sample_nonzero t B r s hs _ v (hr v),
      sample_nonzero t B r s hs _ w (hr w)⟩
    exact sample_zero t B r s hs ht _ w v (fun i hi hj => Finset.mem_inter.mpr ⟨hj,hi⟩)
      (he w v hvw.symm)

#print axioms sample_nonzero
#print axioms sample_zero
#print axioms cover
end Erdos595AlgebraicSupportCover
