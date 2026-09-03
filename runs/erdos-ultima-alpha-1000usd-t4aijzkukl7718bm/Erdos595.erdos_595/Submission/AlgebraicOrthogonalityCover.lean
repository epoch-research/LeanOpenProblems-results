import Submission.PolynomialOrthogonalityCover
import Submission.LocalTupleCover

/-!
Countably dimensional field extensions preserve countable triangle-free edge
coverability for all finite-dimensional nonisotropic bilinear graphs.
This extends the rational-function exclusion, not the main conjecture.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open SimpleGraph Set Module
open scoped BigOperators
namespace Erdos595AlgebraicOrthogonality
open Erdos595Work Erdos595PolynomialOrthogonality

variable {K : Type*} [Field K]
variable {E : Type*} [AddCommGroup E] [Module K E]

abbrev Point (B : LinearMap.BilinForm K E) := {x : E // B x x ≠ 0}

def graph (B : LinearMap.BilinForm K E) : SimpleGraph (Point B) where
  Adj x y := B x.val y.val = 0 ∧ B y.val x.val = 0
  symm := fun _ _ h => h.symm
  loopless := fun x h => x.property h.1

/-- A property of a field, quantified over all finite dimensions and matrices. -/
def FiniteFormsCover (K : Type*) [Field K] : Prop :=
  ∀ n : ℕ, ∀ B : LinearMap.BilinForm K (Fin n → K),
    IsCountableUnionOfTriangleFree (graph B)

theorem cover_of_finite_representation [FiniteDimensional K E]
    (hK : FiniteFormsCover K) {V : Type*} (G : SimpleGraph V)
    (B : LinearMap.BilinForm K E) (r : V → E)
    (hr : ∀ v, B (r v) (r v) ≠ 0)
    (he : ∀ a b, G.Adj a b → B (r a) (r b) = 0) :
    IsCountableUnionOfTriangleFree G := by
  classical
  let e := (Module.finBasis K E).equivFun
  let D := LinearMap.BilinForm.congr e B
  have hd (x y : E) : D (e x) (e y) = B x y := by simp [D]
  let f : G →g graph D :=
    ⟨fun v => ⟨e (r v),by simpa only [hd] using hr v⟩,
      fun h => ⟨by rw [hd]; exact he _ _ h,by rw [hd]; exact he _ _ h.symm⟩⟩
  exact countable_union_of_hom f (hK _ D)

theorem cover_finite_form [FiniteDimensional K E] (hK : FiniteFormsCover K)
    (B : LinearMap.BilinForm K E) : IsCountableUnionOfTriangleFree (graph B) :=
  cover_of_finite_representation hK (graph B) B Subtype.val (fun v => v.property)
    (fun _ _ h => h.1)

/-- Countably dimensional spaces are unions of countably many finite-support
subspaces. Arbitrary subsets of their nonisotropic points inherit the cover. -/
theorem cover_of_countable_representation {J : Type*} [Countable J]
    (hK : FiniteFormsCover K) (b : Basis J K E) {V : Type*} (G : SimpleGraph V)
    (B : LinearMap.BilinForm K E) (r : V → E)
    (hr : ∀ v, B (r v) (r v) ≠ 0)
    (he : ∀ a b, G.Adj a b → B (r a) (r b) = 0) :
    IsCountableUnionOfTriangleFree G := by
  classical
  let idx (v : V) := (b.repr (r v)).support
  apply Erdos595LocalTuple.cover_of_countable_fibers G idx
  intro T
  let M := Submodule.span K (b '' (T : Set J))
  haveI : FiniteDimensional K M :=
    FiniteDimensional.span_of_finite K (T.finite_toSet.image b)
  let r' : {v : V // idx v = T} → M := fun v => ⟨r v.val,by
    have ht : (b.repr (r v.val)).support = T := v.property
    simpa only [ht] using b.mem_span_repr_support (r v.val)⟩
  let D := B.comp M.subtype M.subtype
  apply cover_of_finite_representation hK _ D r'
  · intro v
    exact hr v.val
  · intro v w h
    exact he v.val w.val h

section Rational
variable {R I : Type*} [CommRing R] [IsDomain R] [Countable R]
variable [Algebra (MvPolynomial I R) K] [IsFractionRing (MvPolynomial I R) K]

include R I in
/-- Rational-function fields over countable domains satisfy the field property. -/
theorem rational_field : FiniteFormsCover K := by
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
  apply cover_of_fraction_matrix (R := R) (I := I) M (graph B) Subtype.val
  · intro v
    simpa only [hm] using v.property
  · intro a b h
    simpa only [hm] using h.1
end Rational

section Extension
variable {F : Type*} [Field F] [Algebra K F] [FiniteDimensional K F]

/-- Project to a nonzero coordinate of the diagonal value in a field basis.
Within each resulting fiber, restriction of scalars gives a nonisotropic
K-bilinear representation. There are only finitely many fibers. -/
theorem finite_extension (hK : FiniteFormsCover K) : FiniteFormsCover F := by
  classical
  intro n B
  let b := Module.finBasis K F
  have hex (x : Point B) : ∃ i, b.coord i (B x.val x.val) ≠ 0 := by
    by_contra h
    push_neg at h
    apply x.property
    apply b.repr.injective
    ext i
    simpa only [map_zero,Finsupp.zero_apply] using h i
  choose idx hidx using hex
  apply Erdos595LocalTuple.cover_of_countable_fibers (graph B) idx
  intro i
  let D : LinearMap.BilinForm K (Fin n → F) :=
    (B.restrictScalars₁₂ K K).compr₂ (b.coord i)
  let r : {x : Point B // idx x = i} → (Fin n → F) := fun x => x.val.val
  apply cover_of_finite_representation hK _ D r
  · intro x
    change b.coord i (B x.val.val x.val.val) ≠ 0
    simpa only [x.property] using hidx x.val
  · intro x y h
    change b.coord i (B x.val.val y.val.val) = 0
    have hz : B x.val.val y.val.val = 0 := h.1
    rw [hz,map_zero]
end Extension

section CountableExtension
variable {F J : Type*} [Field F] [Algebra K F] [Countable J]

/-- A countable basis of the extension suffices. Algebraicity is not assumed. -/
theorem countable_extension (hK : FiniteFormsCover K) (b : Basis J K F) :
    FiniteFormsCover F := by
  classical
  intro n B
  have hex (x : Point B) : ∃ i, b.coord i (B x.val x.val) ≠ 0 := by
    by_contra h
    push_neg at h
    apply x.property
    apply b.repr.injective
    ext i
    simpa only [map_zero,Finsupp.zero_apply] using h i
  choose idx hidx using hex
  apply Erdos595LocalTuple.cover_of_countable_fibers (graph B) idx
  intro i
  let D : LinearMap.BilinForm K (Fin n → F) :=
    (B.restrictScalars₁₂ K K).compr₂ (b.coord i)
  let r : {x : Point B // idx x = i} → (Fin n → F) := fun x => x.val.val
  apply cover_of_countable_representation hK (Pi.basis (fun _ : Fin n => b)) _ D r
  · intro x
    change b.coord i (B x.val.val x.val.val) ≠ 0
    simpa only [x.property] using hidx x.val
  · intro x y h
    change b.coord i (B x.val.val y.val.val) = 0
    have hz : B x.val.val y.val.val = 0 := h.1
    rw [hz,map_zero]
end CountableExtension

#print axioms cover_of_finite_representation
#print axioms rational_field
#print axioms finite_extension
#print axioms cover_of_countable_representation
#print axioms countable_extension
end Erdos595AlgebraicOrthogonality
