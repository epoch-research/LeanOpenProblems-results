import Submission.AlgebraicSupportCover
import Submission.AlgebraicOrthogonalityCover

/-!
Nonisotropic finite-dimensional bilinear graphs over every field have countable
triangle-free edge covers. This excludes all such geometric candidates. It
provides no universal representation of K4-free graphs and does not settle
Erdős 595.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open Set SimpleGraph
open scoped BigOperators
namespace Erdos595AllFieldOrthogonality
open Erdos595Work Erdos595PolynomialOrthogonality

section Closed
variable {L J V : Type*} [Field L] [IsAlgClosed L] [Fintype J]

/-- First prove the matrix statement in an algebraically closed overfield. -/
theorem cover_matrix_closed (B : J → J → L) (G : SimpleGraph V) (r : V → J → L)
    (hr : ∀ v, form B (RingHom.id L) (r v) (r v) ≠ 0)
    (he : ∀ v w, G.Adj v w → form B (RingHom.id L) (r v) (r w) = 0) :
    IsCountableUnionOfTriangleFree G := by
  classical
  let S : Set L := range (fun ij : J × J => B ij.1 ij.2)
  let F : Subfield L := Subfield.closure S
  haveI : Countable S := (Set.finite_range _).countable.to_subtype
  letI : Countable F := Cardinal.mk_le_aleph0_iff.mp
    ((Subfield.cardinalMk_closure_le_max S).trans (max_le Cardinal.mk_le_aleph0 le_rfl))
  let C : J → J → F := fun i j => ⟨B i j,Subfield.subset_closure ⟨(i,j),rfl⟩⟩
  obtain ⟨I,t,ht⟩ := exists_isTranscendenceBasis' F L
  have hex (v : V) : ∃ s : Finset I, ∀ j,
      r v j ∈ Erdos595AlgebraicSupportFields.closure F (t '' (s : Set I)) := by
    obtain ⟨s,hs⟩ := Erdos595AlgebraicSupportFields.finite_support F ht (Finset.univ.image (r v))
    exact ⟨s,fun j => hs _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)⟩
  choose s hs using hex
  apply Erdos595AlgebraicSupportCover.cover t C r s hs ht.1 G
  · exact hr
  · exact he

end Closed

section Arbitrary
variable {K J V : Type*} [Field K] [Fintype J]

/-- The field and vertex cardinalities are unrestricted. -/
theorem cover_matrix (B : J → J → K) (G : SimpleGraph V) (r : V → J → K)
    (hr : ∀ v, form B (RingHom.id K) (r v) (r v) ≠ 0)
    (he : ∀ v w, G.Adj v w → form B (RingHom.id K) (r v) (r w) = 0) :
    IsCountableUnionOfTriangleFree G := by
  let L := AlgebraicClosure K
  letI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let f := algebraMap K L
  let C : J → J → L := fun i j => f (B i j)
  let q : V → J → L := fun v j => f (r v j)
  have hm (v w : V) : f (form B (RingHom.id K) (r v) (r w)) =
      form C (RingHom.id L) (q v) (q w) := by
    simp only [form,map_sum,map_mul,RingHom.id_apply,C,q]
  apply cover_matrix_closed C G q
  · intro v hv
    apply hr v
    apply RingHom.injective f
    rw [hm,hv,map_zero]
  · intro v w hvw
    rw [← hm,he v w hvw,map_zero]

/-- All finite-dimensional nonisotropic bilinear graphs over K are covered. -/
theorem finiteFormsCover (K : Type*) [Field K] :
    Erdos595AlgebraicOrthogonality.FiniteFormsCover K := by
  classical
  intro n B
  let M := B.toMatrix'
  have hm (x y : Fin n → K) : form M (RingHom.id K) x y = B x y := by
    rw [← Matrix.toBilin'_toMatrix' B]
    simp only [Matrix.toBilin'_apply,form,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [M]
    ring
  apply cover_matrix M (Erdos595AlgebraicOrthogonality.graph B) Subtype.val
  · intro v
    simpa only [hm] using v.property
  · intro v w h
    simpa only [hm] using h.1

/-- A convenient representation formulation of the field-independent theorem. -/
theorem cover_of_finite_representation {E : Type*} [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (G : SimpleGraph V) (B : LinearMap.BilinForm K E)
    (r : V → E) (hr : ∀ v, B (r v) (r v) ≠ 0)
    (he : ∀ a b, G.Adj a b → B (r a) (r b) = 0) :
    IsCountableUnionOfTriangleFree G :=
  Erdos595AlgebraicOrthogonality.cover_of_finite_representation (finiteFormsCover K) G B r hr he

end Arbitrary

#print axioms cover_matrix_closed
#print axioms cover_matrix
#print axioms finiteFormsCover
#print axioms cover_of_finite_representation
end Erdos595AllFieldOrthogonality
