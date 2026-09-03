import Submission.PositiveIndexTwoObstruction
import Submission.Work

/-!
The cone over the Mycielski graph of C5 is a finite K4-free graph with no
real positive-index-three orthogonality representation, even allowing an
arbitrary positive semidefinite negative bilinear space. This rules out a
universal real representation shortcut; it does not settle Erdos 595.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
open SimpleGraph Set
open scoped RealInnerProductSpace
namespace Erdos595PositiveIndexThreeConeObstruction
open Erdos595PositiveIndexTwoObstruction

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  (Q : LinearMap.BilinForm ℝ E)
  (hs : ∀ x y, Q x y = Q y x) (hp : ∀ x, 0 ≤ Q x x)

noncomputable def reduced (u : E) (r : ℝ) : LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (fun x y => Q x y - Q u x * Q u y / r)
    (by intros; simp only [map_add,LinearMap.add_apply]; ring)
    (by intros; simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]; ring)
    (by intros; simp only [map_add]; ring)
    (by intros; simp only [map_smul,smul_eq_mul]; ring)

@[simp] lemma reduced_apply (u x y : E) (r : ℝ) :
    reduced Q u r x y = Q x y - Q u x * Q u y / r := rfl

include hs in
lemma reduced_symm (u : E) (r : ℝ) (x y : E) :
    reduced Q u r x y = reduced Q u r y x := by
  simp only [reduced_apply]
  rw [hs x y,mul_comm (Q u x)]

include hs hp in
lemma reduced_nonneg (u : E) {r : ℝ} (hr : Q u u < r) (x : E) :
    0 ≤ reduced Q u r x x := by
  have hrpos : 0 < r := lt_of_le_of_lt (hp u) hr
  have h := hp (x - (Q u x / r) • u)
  simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul] at h
  rw [hs x u] at h
  have hm : (Q u x / r)^2 * Q u u ≤ (Q u x / r)^2 * r :=
    mul_le_mul_of_nonneg_left (le_of_lt hr) (sq_nonneg _)
  have hid : Q x x - Q u x * Q u x / r =
      Q x x - 2*(Q u x / r)*Q u x + (Q u x / r)^2*r := by
    field_simp
    ring
  rw [reduced_apply,hid]
  nlinarith

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [Fact (Module.finrank ℝ P = 3)]

noncomputable def planePoint (a v : P) (ha : a ≠ 0) : (ℝ ∙ a)ᗮ := by
  refine ⟨v - (⟪a,v⟫ / ⟪a,a⟫) • a, ?_⟩
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp only [inner_sub_right,inner_smul_right]
  rw [div_mul_cancel₀ _ (real_inner_self_pos.mpr ha).ne']
  exact sub_self _

omit [Fact (Module.finrank ℝ P = 3)] in
lemma planePoint_inner (a v w : P) (ha : a ≠ 0) :
    ⟪planePoint a v ha, planePoint a w ha⟫ =
      ⟪v,w⟫ - ⟪a,v⟫ * ⟪a,w⟫ / ⟪a,a⟫ := by
  change ⟪v-(⟪a,v⟫ / ⟪a,a⟫) • a,
    w-(⟪a,w⟫ / ⟪a,a⟫) • a⟫ = _
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,inner_smul_right]
  rw [real_inner_comm v a]
  field_simp
  ring

abbrev ConeVertex := Option MVertex
abbrev cone := Erdos595Work.coneGraph MGraph

lemma cone_cliqueFree : cone.CliqueFree 4 :=
  Erdos595Work.coneGraph_cliqueFree MGraph Erdos595MycielskiFiveOrder.triangleFree

lemma cone_covered : Erdos595Work.IsCountableUnionOfTriangleFree cone :=
  Erdos595Work.countable_union_coneGraph MGraph Erdos595MycielskiFiveOrder.triangleFree

lemma cone_card : Fintype.card ConeVertex = 12 := by decide +kernel

include hs hp in
/-- The negative bilinear space has no dimension or nondegeneracy restriction. -/
theorem no_representation (p : ConeVertex → P) (q : ConeVertex → E)
    (hr : ∀ v, 0 < ⟪p v,p v⟫ - Q (q v) (q v))
    (he : ∀ a b, cone.Adj a b → ⟪p a,p b⟫ - Q (q a) (q b) = 0) : False := by
  classical
  let a := p none
  let u := q none
  let r := ⟪a,a⟫
  have hu : Q u u < r := by have h := hr none; exact sub_pos.mp h
  have hapos : 0 < ⟪a,a⟫ := lt_of_le_of_lt (hp u) hu
  have ha : a ≠ 0 := real_inner_self_pos.mp hapos
  let B : OrthonormalBasis (Fin 2) ℝ (ℝ ∙ a)ᗮ :=
    OrthonormalBasis.fromOrthogonalSpanSingleton 2 ha
  let f : MVertex → EuclideanSpace ℝ (Fin 2) := fun v => B.repr (planePoint a (p (some v)) ha)
  let Q' := reduced Q u r
  have hf (v w : MVertex) :
      f v 0 * f w 0 + f v 1 * f w 1 - Q' (q (some v)) (q (some w)) =
        ⟪p (some v),p (some w)⟫ - Q (q (some v)) (q (some w)) := by
    have hb := B.repr.inner_map_map (planePoint a (p (some v)) ha)
      (planePoint a (p (some w)) ha)
    change ⟪f v,f w⟫ = _ at hb
    rw [planePoint_inner] at hb
    have hv := he none (some v) trivial
    have hw := he none (some w) trivial
    have hv' : ⟪a,p (some v)⟫ = Q u (q (some v)) := sub_eq_zero.mp hv
    have hw' : ⟪a,p (some w)⟫ = Q u (q (some w)) := sub_eq_zero.mp hw
    rw [hv',hw'] at hb
    have hi : ⟪f v,f w⟫ = f v 0*f w 0 + f v 1*f w 1 := by
      simp [PiLp.inner_apply,Fin.sum_univ_two,mul_comm]
    rw [hi] at hb
    dsimp only [Q']
    rw [reduced_apply,hb]
    dsimp only [r]
    ring
  apply Erdos595PositiveIndexTwoObstruction.no_representation Q'
    (reduced_symm Q hs u r) (reduced_nonneg Q hs hp u hu)
    (fun v => f v 0) (fun v => f v 1) (fun v => q (some v))
  · intro v
    rw [hf]
    exact hr (some v)
  · intro v w hvw
    rw [hf]
    exact he (some v) (some w) hvw

#print axioms reduced_nonneg
#print axioms planePoint_inner
#print axioms cone_cliqueFree
#print axioms cone_covered
#print axioms cone_card
#print axioms no_representation
end Erdos595PositiveIndexThreeConeObstruction
