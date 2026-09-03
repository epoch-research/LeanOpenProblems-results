import Submission.AllFieldOrthogonalityCover

/-!
Orthogonality with finitely many positive coordinates and an arbitrary number
of finitely supported negative coordinates is countably triangle-free-edge
coverable, over any ordered field. This is another candidate exclusion, not
an assertion that every K4-free graph has such a representation.
-/
set_option autoImplicit false
open Set SimpleGraph
open scoped BigOperators
namespace Erdos595DiagonalPositiveIndex
open Erdos595Work

variable {K I P V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype P]

noncomputable def negDot (x y : I →₀ K) : K := x.sum (fun i a => a * y i)

lemma negDot_inter [DecidableEq I] (x y : I →₀ K) :
    negDot x y = ∑ i ∈ x.support ∩ y.support, x i * y i := by
  symm
  apply Finset.sum_subset Finset.inter_subset_left
  intro i hi hn
  have hy : i ∉ y.support := fun hy => hn (Finset.mem_inter.mpr ⟨hi,hy⟩)
  rw [Finsupp.notMem_support_iff.mp hy,mul_zero]

lemma negDot_restrict_le (x : I →₀ K) (R : Finset I) :
    (∑ i : R, x i.val * x i.val) ≤ negDot x x := by
  classical
  rw [Finset.sum_coe_sort R (fun i => x i * x i)]
  have he : (∑ i ∈ R ∩ x.support, x i * x i) = ∑ i ∈ R, x i * x i := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro i hi hn
    have hx : i ∉ x.support := fun hx => hn (Finset.mem_inter.mpr ⟨hi,hx⟩)
    rw [Finsupp.notMem_support_iff.mp hx,zero_mul]
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    (fun i _ _ => mul_self_nonneg (x i))

noncomputable def localBilin (R : Finset I) :
    LinearMap.BilinForm K ((P → K) × (R → K)) :=
  LinearMap.mk₂ K (fun x y => x.1 ⬝ᵥ y.1 - x.2 ⬝ᵥ y.2)
    (by intros; simp only [Prod.fst_add,Prod.snd_add,add_dotProduct]; ring)
    (by intros; simp only [Prod.smul_fst,Prod.smul_snd,smul_dotProduct,smul_eq_mul]; ring)
    (by intros; simp only [Prod.fst_add,Prod.snd_add,dotProduct_add]; ring)
    (by intros; simp only [Prod.smul_fst,Prod.smul_snd,dotProduct_smul,smul_eq_mul]; ring)

@[simp] lemma localBilin_apply (R : Finset I) (x y : (P → K) × (R → K)) :
    localBilin R x y = x.1 ⬝ᵥ y.1 - x.2 ⬝ᵥ y.2 := rfl

variable (G : SimpleGraph V) (p : V → P → K) (q : V → I →₀ K)
  (hr : ∀ v, 0 < p v ⬝ᵥ p v - negDot (q v) (q v))

noncomputable def project (R : Finset I) (v : V) :
    Erdos595AlgebraicOrthogonality.Point (localBilin (K := K) (P := P) R) := by
  refine ⟨(p v,fun i : R => q v i.val),?_⟩
  change p v ⬝ᵥ p v - (∑ i : R, q v i.val * q v i.val) ≠ 0
  have h := negDot_restrict_le (q v) R
  have hv := hr v
  exact ne_of_gt (lt_of_lt_of_le hv (sub_le_sub_left h _))

lemma projected_cross [DecidableEq I] (a b : V) :
    localBilin ((q a).support ∩ (q b).support)
      (project p q hr _ a).val (project p q hr _ b).val =
      p a ⬝ᵥ p b - negDot (q a) (q b) := by
  change p a ⬝ᵥ p b - (∑ i : ↥((q a).support ∩ (q b).support), q a i.val * q b i.val) = _
  rw [Finset.sum_coe_sort _ (fun i => q a i * q b i),negDot_inter]

include hr in
/-- Finite positive index plus diagonal finite negative support is sufficient;
there is no cardinality restriction on I, K, or V. -/
theorem cover
    (he : ∀ a b, G.Adj a b → p a ⬝ᵥ p b - negDot (q a) (q b) = 0) :
    IsCountableUnionOfTriangleFree G := by
  classical
  apply Erdos595PointCountableEdgeCover.finite_intersection_reduction G (fun v => (q v).support)
    (fun R => Erdos595AlgebraicOrthogonality.Point (localBilin (K := K) (P := P) R))
    (fun R => Erdos595AlgebraicOrthogonality.graph (localBilin (K := K) (P := P) R))
    (project p q hr)
  · intro R
    exact Erdos595AlgebraicOrthogonality.cover_finite_form
      (Erdos595AllFieldOrthogonality.finiteFormsCover K) _
  · intro a b hab
    constructor
    · rw [projected_cross]
      exact he a b hab
    · rw [Finset.inter_comm,projected_cross]
      exact he b a hab.symm

#print axioms negDot_restrict_le
#print axioms cover
end Erdos595DiagonalPositiveIndex
