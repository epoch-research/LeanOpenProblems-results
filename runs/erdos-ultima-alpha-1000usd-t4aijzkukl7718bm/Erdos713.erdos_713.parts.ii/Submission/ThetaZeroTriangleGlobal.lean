import FormalConjecturesUtil
import Submission.ThetaZeroTriangle
import Submission.ConditionalThetaWeighted

/-! A whole-host consequence of an ADDITIONAL link hypothesis.
Absence of zero-codegree triangles is not deduced from theta-freeness. -/
open Finset
namespace Erdos713ThetaZeroTriangleGlobal
open Erdos713ThetaGram Erdos713GlobalLight Erdos713GlobalTheta
open Erdos713ConditionalThetaWeighted Erdos713ThetaZeroTriangle
variable {A B : Type*}
set_option maxHeartbeats 2000000

/-- Summing the local density gap avoids all upper-degree and almost-regularity
hypotheses. The extra zero-triangle exclusion is required at every root. -/
theorem sum_row_squares [Fintype A] [Fintype B] (R : A → B → Prop)
    (hf : ∀ a, ¬ HasTheta (link R a)) (hz : ∀ a, NoZeroTriangle (link R a)) :
    (∑ a : A, (Nat.card {b // R a b})^2) ≤
      12*(Fintype.card A)^2+6*(Fintype.card B)^2 := by
  classical
  have hlocal (a : A) : (Nat.card {b // R a b})^2 ≤
      12*Fintype.card A+2*(lightPairs R 3 a).card := by
    have h := density_gap (hf a) (hz a)
    rw [link_lightCount] at h
    have hm : Fintype.card {x : A // x ≠ a} ≤ Fintype.card A :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    simp only [Nat.card_eq_fintype_card] at h ⊢
    omega
  have hs := sum_le_sum (s := (univ : Finset A)) (fun a _ => hlocal a)
  have ht := sum_lightPairs_le R 3
  simp only [sum_add_distrib,sum_const,card_univ,Nat.nsmul_eq_mul,← mul_sum] at hs
  nlinarith only [hs,ht]

/-- A conditional incidence bound, without regularization or any minimum
or maximum degree assumptions. -/
theorem incidence_square [Fintype A] [Fintype B] (R : A → B → Prop)
    (hf : ∀ a, ¬ HasTheta (link R a)) (hz : ∀ a, NoZeroTriangle (link R a)) :
    (Nat.card {p : A × B // R p.1 p.2})^2 ≤
      12*(Fintype.card A)^3+6*Fintype.card A*(Fintype.card B)^2 := by
  classical
  rw [Erdos713ThetaSplit.edge_card_eq_rows]
  have hc := sq_sum_le_card_mul_sum_sq (s := (univ : Finset A))
    (f := fun a => Nat.card {b // R a b})
  rw [card_univ] at hc
  have hu := Nat.mul_le_mul_left (Fintype.card A) (sum_row_squares R hf hz)
  nlinarith only [hc,hu]

theorem balanced_incidence_square (n : ℕ) (R : Fin n → Fin n → Prop)
    (hf : ∀ a, ¬ HasTheta (link R a)) (hz : ∀ a, NoZeroTriangle (link R a)) :
    (Nat.card {p : Fin n × Fin n // R p.1 p.2})^2 ≤ 18*n^3 := by
  have h := incidence_square R hf hz
  simp only [Fintype.card_fin] at h
  nlinarith only [h]

/-- For balanced shores, minimum row degree already suffices. -/
theorem minimum_degree_square (n d : ℕ) (hn : 0 < n) (R : Fin n → Fin n → Prop)
    (hf : ∀ a, ¬ HasTheta (link R a)) (hz : ∀ a, NoZeroTriangle (link R a))
    (hd : ∀ a, d ≤ Nat.card {b // R a b}) : d^2 ≤ 18*n := by
  classical
  have hlow : n*d^2 ≤ ∑ a : Fin n, (Nat.card {b // R a b})^2 := by
    calc
      _ = ∑ _a : Fin n, d^2 := by simp
      _ ≤ _ := sum_le_sum (fun a _ => Nat.pow_le_pow_left (hd a) 2)
  have hu := sum_row_squares R hf hz
  simp only [Fintype.card_fin] at hu
  have hmul : n*d^2 ≤ n*(18*n) := by nlinarith only [hlow,hu]
  exact Nat.le_of_mul_le_mul_left hmul hn

/-- If the extra link condition fails, its negation supplies an actual triple,
not a rate assertion or an asymptotic conclusion. -/
lemma zero_triangle_of_not [Fintype A] (R : A → B → Prop) (h : ¬ NoZeroTriangle R) :
    ∃ x y z : B, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      codegree R x y = 0 ∧ codegree R x z = 0 ∧ codegree R y z = 0 := by
  classical
  by_contra hn
  apply h
  intro x y z hxy hxz hyz h1 h2 h3
  exact hn ⟨x,y,z,hxy,hxz,hyz,h1,h2,h3⟩

/-- Consequently a super-square-degree, theta-free-link host must contain
three neighbours of one root for which every pair has global codegree ONE.
This is NOT a contradiction: such triples are not forbidden in general. -/
theorem exists_codegree_one_triple (n d : ℕ) (hn : 0 < n)
    (R : Fin n → Fin n → Prop) (hf : ∀ a, ¬ HasTheta (link R a))
    (hd : ∀ a, d ≤ Nat.card {b // R a b}) (hlarge : 18*n < d^2) :
    ∃ (a : Fin n) (x y z : Fin n), x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      R a x ∧ R a y ∧ R a z ∧ codegree R x y = 1 ∧
      codegree R x z = 1 ∧ codegree R y z = 1 := by
  classical
  have hnot : ¬ ∀ a, NoZeroTriangle (link R a) := by
    intro hz
    have h := minimum_degree_square n d hn R hf hz hd
    omega
  obtain ⟨a,ha⟩ := not_forall.mp hnot
  obtain ⟨x,y,z,hxy,hxz,hyz,h1,h2,h3⟩ := zero_triangle_of_not (link R a) ha
  refine ⟨a,x.val,y.val,z.val,?_,?_,?_,x.property,y.property,z.property,?_,?_,?_⟩
  · exact fun he => hxy (Subtype.ext he)
  · exact fun he => hxz (Subtype.ext he)
  · exact fun he => hyz (Subtype.ext he)
  · have h := link_codegree_add_one R a x y
    omega
  · have h := link_codegree_add_one R a x z
    omega
  · have h := link_codegree_add_one R a y z
    omega

/-- The same forced configuration follows directly from a large edge
count. No minimum-degree selection is needed. -/
theorem exists_codegree_one_triple_of_edges (n : ℕ)
    (R : Fin n → Fin n → Prop) (hf : ∀ a, ¬ HasTheta (link R a))
    (hlarge : 18*n^3 < (Nat.card {p : Fin n × Fin n // R p.1 p.2})^2) :
    ∃ (a : Fin n) (x y z : Fin n), x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      R a x ∧ R a y ∧ R a z ∧ codegree R x y = 1 ∧
      codegree R x z = 1 ∧ codegree R y z = 1 := by
  classical
  have hnot : ¬ ∀ a, NoZeroTriangle (link R a) := by
    intro hz
    have h := balanced_incidence_square n R hf hz
    omega
  obtain ⟨a,ha⟩ := not_forall.mp hnot
  obtain ⟨x,y,z,hxy,hxz,hyz,h1,h2,h3⟩ := zero_triangle_of_not (link R a) ha
  refine ⟨a,x.val,y.val,z.val,?_,?_,?_,x.property,y.property,z.property,?_,?_,?_⟩
  · exact fun he => hxy (Subtype.ext he)
  · exact fun he => hxz (Subtype.ext he)
  · exact fun he => hyz (Subtype.ext he)
  · have h := link_codegree_add_one R a x y
    omega
  · have h := link_codegree_add_one R a x z
    omega
  · have h := link_codegree_add_one R a y z
    omega

#print axioms sum_row_squares
#print axioms incidence_square
#print axioms balanced_incidence_square
#print axioms minimum_degree_square
#print axioms exists_codegree_one_triple
#print axioms exists_codegree_one_triple_of_edges
end Erdos713ThetaZeroTriangleGlobal
