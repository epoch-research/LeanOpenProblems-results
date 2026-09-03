import FormalConjecturesUtil
import Submission.ThetaDisjointSupports
import Submission.ThetaAnchorBudget

/-! A cubic minimum-column-degree bound for an oriented-theta-free
relation with minimum row degree four. No square-degree bound is asserted. -/
open Finset
namespace Erdos713ThetaMinimumColumnCubic
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaAnchorPacking Erdos713ThetaAnchorBudget
open Erdos713ThetaDisjointSupports
variable {A B : Type*}
set_option maxHeartbeats 2000000

lemma commonRows_univ_card [Fintype A] [Fintype B] (R : A → B → Prop) (p : B × B) :
    (commonRows R univ p).card = codegree R p.1 p.2 := by
  classical
  simp only [commonRows,codegree,Nat.card_eq_fintype_card,Fintype.card_subtype]

/-- Large codegrees are bounded by the disjoint supporting-row budget;
small codegrees are handled separately. -/
lemma codegree_times_min_column [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hrow : ∀ a : A, 4 ≤ (row R a).card)
    (d : ℕ) (hd : ∀ x : B, d ≤ Nat.card {a // R a x})
    (x y : B) (hxy : x ≠ y) :
    codegree R x y*d ≤ max (Fintype.card A) (2*d) := by
  classical
  by_cases hh : 3 ≤ codegree R x y
  · have h := book_size_mul_min_column_le_rows (p := (x,y)) hf (univ : Finset A) hxy hh
      (fun a _ => hrow a) d hd
    rw [commonRows_univ_card] at h
    exact h.trans (le_max_left _ _)
  · have hsmall : codegree R x y ≤ 2 := by omega
    exact (Nat.mul_le_mul_right d hsmall).trans (le_max_right _ _)

/-- In a nonempty column set, minimum row degree four and theta exclusion
force `3*d^3 <= 8*m^2`, where `m` is the number of rows. -/
theorem minimum_column_cubic [Fintype A] [Fintype B] [Nonempty B]
    {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hrow : ∀ a : A, 4 ≤ (row R a).card)
    (d : ℕ) (hd : ∀ x : B, d ≤ Nat.card {a // R a x}) :
    3*d^3 ≤ 8*(Fintype.card A)^2 := by
  classical
  let m := Fintype.card A
  let k := Fintype.card B
  let E := ∑ a : A, (row R a).card
  let Q := ∑ a : A, (row R a).offDiag.card
  let Z := ∑ a : A, (row R a).card^2
  have hk : 0 < k := Fintype.card_pos
  have hd_le : d ≤ m := by
    obtain ⟨x⟩ := ‹Nonempty B›
    apply (hd x).trans
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  have hmax : max m (2*d) ≤ 2*m := max_le (by omega) (by omega)
  have hc : E^2 ≤ m*Z := by
    simpa only [E,Z,m,card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := (univ : Finset A)) (f := fun a => (row R a).card))
  have hZ : 3*Z ≤ 4*Q := by
    dsimp only [Z,Q]
    rw [mul_sum,mul_sum]
    apply sum_le_sum
    intro a _
    have hr := hrow a
    rw [offDiag_card]
    have hs : (row R a).card*(row R a).card-(row R a).card+(row R a).card =
        (row R a).card*(row R a).card :=
      Nat.sub_add_cancel (by nlinarith)
    nlinarith
  have hQ : d*Q ≤ 2*m*k^2 := by
    have hpair := pair_incidence_sum R (univ : Finset A)
    change Q = _ at hpair
    rw [hpair,mul_sum]
    calc
      _ ≤ ∑ _p ∈ (univ : Finset B).offDiag, 2*m := by
        apply sum_le_sum
        intro p hp
        have h := codegree_times_min_column hf hrow d hd p.1 p.2 (mem_offDiag.mp hp).2.2
        rw [commonRows_univ_card]
        have hh : d*codegree R p.1 p.2 ≤ max m (2*d) := by
          simpa only [Nat.mul_comm,m] using h
        exact hh.trans hmax
      _ = (univ : Finset B).offDiag.card*(2*m) := by simp
      _ ≤ k^2*(2*m) := by
        apply Nat.mul_le_mul_right
        simp only [offDiag_card,card_univ,k,pow_two]
        exact Nat.sub_le _ _
      _ = _ := by ring
  have hE : k*d ≤ E := by
    have hdouble := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
      (s := (univ : Finset A)) (t := (univ : Finset B))
    have he : E = ∑ x : B, Nat.card {a // R a x} := by
      simpa only [E,row,bipartiteAbove,bipartiteBelow,Nat.card_eq_fintype_card,
        Fintype.card_subtype] using hdouble
    rw [he]
    calc
      _ = ∑ _x : B, d := by simp [k]
      _ ≤ _ := sum_le_sum (fun x _ => hd x)
  have hEc : 3*E^2 ≤ 4*m*Q := by
    have h1 := Nat.mul_le_mul_left 3 hc
    have h2 := Nat.mul_le_mul_left m hZ
    nlinarith only [h1,h2]
  have hfin : 3*d^3*k^2 ≤ 8*m^2*k^2 := by
    have h1 := Nat.pow_le_pow_left hE 2
    have h2 := Nat.mul_le_mul_left (3*d) h1
    have h3 := Nat.mul_le_mul_left d hEc
    have h4 := Nat.mul_le_mul_left (4*m) hQ
    nlinarith only [h2,h3,h4]
  exact Nat.le_of_mul_le_mul_right hfin (by positivity : 0 < k^2)

#print axioms codegree_times_min_column
#print axioms minimum_column_cubic
end Erdos713ThetaMinimumColumnCubic
