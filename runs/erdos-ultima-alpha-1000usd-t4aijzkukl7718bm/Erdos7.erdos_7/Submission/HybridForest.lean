import Submission.ForestEvents
import Submission.BinaryRootOverlap

/-! Forests with several compensated root edges and ordinary product edges.
The estimates here have no exponent-cap or class-count restriction. -/
namespace Erdos7HybridForest
open scoped BigOperators
open Erdos7ForestUnion Erdos7ForestCapacity Erdos7ForestEvents
set_option maxHeartbeats 2000000
set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma compensation_sum (O R : Finset (ι × ι)) (a w : ι → ℚ) (haw : ∀ i,a i ≤ w i)
    (c d : ℚ) (I : ι × ι → ℚ)
    (hroot : ∀ e ∈ R,c*w e.1*w e.2 ≤ I e +
      d*((w e.1-a e.1)*w e.2+w e.1*(w e.2-a e.2)))
    (hdegree : ∀ i,neighbor O w i+d*neighbor R w i ≤ 1) :
    c*edgeProduct R w ≤ (∑ e ∈ R,I e) +
      ∑ i,(w i-a i)*(1-neighbor O w i) := by
  have hs := Finset.sum_le_sum hroot
  have he : (∑ e ∈ R,c*w e.1*w e.2) = c*edgeProduct R w := by
    simp only [edgeProduct,Finset.mul_sum,mul_assoc]
  rw [he,Finset.sum_add_distrib,← Finset.mul_sum,← sum_neighbor R (fun i => w i-a i) w] at hs
  have hcap : d*(∑ i,(w i-a i)*neighbor R w i) ≤
      ∑ i,(w i-a i)*(1-neighbor O w i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_le_mul_of_nonneg_left
      (show d*neighbor R w i ≤ 1-neighbor O w i by linarith [hdegree i])
      (sub_nonneg.mpr (haw i))
    nlinarith
  linarith

section Events
variable {Ω : Type*} [Fintype Ω]

/-- Product intersections and compensated intersections can coexist in one
forest. Their degree costs add, including all special edges at each vertex. -/
theorem union_bound (μ : Ω → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (A : ι → Ω → Prop) (parent : ι → Option ι) (rank : ι → ℕ)
    (hparent : ∀ i j,parent i = some j → rank j < rank i)
    (E O R : Finset (ι × ι)) (hE : ∀ i j,(i,j) ∈ E ↔ parent i = some j)
    (hpartition : E = O ∪ R) (hdisjoint : Disjoint O R)
    (w : ι → ℚ) (hw : ∀ i,mass μ (A i) ≤ w i) (c d : ℚ)
    (hprod : ∀ e ∈ O,mass μ (A e.1)*mass μ (A e.2) ≤
      mass μ (fun x => A e.1 x ∧ A e.2 x))
    (hroot : ∀ e ∈ R,c*w e.1*w e.2 ≤ mass μ (fun x => A e.1 x ∧ A e.2 x)+
      d*((w e.1-mass μ (A e.1))*w e.2+w e.1*(w e.2-mass μ (A e.2))))
    (hdegree : ∀ i,neighbor O w i+d*neighbor R w i ≤ 1) :
    mass μ (fun x => ∃ i,A i x) ≤ polynomial O w-c*edgeProduct R w := by
  have hu := weighted_forest_edge_bound μ hμ A parent rank hparent E hE
  rw [hpartition,Finset.sum_union hdisjoint] at hu
  have hp := Finset.sum_le_sum hprod
  have hb : mass μ (fun x => ∃ i,A i x) ≤ polynomial O (fun i => mass μ (A i))-
      ∑ e ∈ R,mass μ (fun x => A e.1 x ∧ A e.2 x) := by
    unfold polynomial edgeProduct
    linarith
  exact compensated_overlap_bound O (fun i => mass μ (A i)) w hw _ _ _ hb
    (compensation_sum O R (fun i => mass μ (A i)) w hw c d
      (fun e => mass μ (fun x => A e.1 x ∧ A e.2 x)) hroot hdegree)

/-- The exponent-independent binary-root estimate in the weight coordinates
used by the forest polynomial. -/
lemma binary_root_charge (t a b A B I : ℚ) (ht : 1/3 ≤ t ∧ t ≤ 2/3)
    (r s : Bool) (ha : 0 ≤ a ∧ a ≤ A) (hb : 0 ≤ b ∧ b ≤ B)
    (hI : (if r = s then Erdos7BinaryRootOverlap.branchMass t r*a*b else 0) ≤ I) :
    (3/2)*((2/3)*A)*((2/3)*B) ≤ I+
      3*(((2/3)*A-Erdos7BinaryRootOverlap.branchMass t r*a)*((2/3)*B)+
        ((2/3)*A)*((2/3)*B-Erdos7BinaryRootOverlap.branchMass t s*b)) := by
  have h := Erdos7BinaryRootOverlap.compensated_pair t a b A B ht r s ha hb
  nlinarith

end Events
#print axioms union_bound
#print axioms binary_root_charge
end Erdos7HybridForest
