import FormalConjecturesUtil
import Submission.ThetaHeavyShadow

/-! A quadratic row-count bound when every distinct column pair is heavy.
This does not establish a stability theorem for a small light-pair budget. -/
open Finset
namespace Erdos713ThetaHeavyRowCount
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
variable {A B : Type*}
set_option maxHeartbeats 2000000

lemma twice_choose_two (n : ℕ) : 2*n.choose 2 = n*n-n := by
  rw [Nat.choose_two_right,Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd,
    Nat.mul_sub_left_distrib,Nat.mul_one]

lemma pair_sum_with_deficit [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hh : Heavy R) :
    (∑ a : A, (row R a).card.choose 2)+(lowRows R).card ≤ 3*Fintype.card A := by
  classical
  have hp (a : A) : (row R a).card.choose 2 +
      2*(if (row R a).card ≤ 2 then 1 else 0) ≤
        (if 4 ≤ (row R a).card then (row R a).card.choose 2 else 0)+3 := by
    by_cases hhi : 4 ≤ (row R a).card
    · have hlo : ¬ (row R a).card ≤ 2 := by omega
      simp [hhi,hlo]
    · have hsmall : (row R a).card ≤ 3 := by omega
      interval_cases he : (row R a).card <;> norm_num
  have hs := sum_le_sum (s := (univ : Finset A)) (fun a _ => hp a)
  have hlow : (∑ a : A, if (row R a).card ≤ 2 then 1 else 0) = (lowRows R).card := by
    simp only [lowRows,card_eq_sum_ones,sum_filter]
  have hhigh : (∑ a : A, if 4 ≤ (row R a).card then (row R a).card.choose 2 else 0) =
      ∑ a ∈ highRows R, (row R a).card.choose 2 := by simp [highRows,sum_filter]
  simp only [sum_add_distrib,← mul_sum,sum_const,card_univ,Nat.nsmul_eq_mul,hlow,hhigh] at hs
  have hh' := high_pairs_le_low_rows hf hh
  omega

lemma pair_sum_eq_codegrees [Fintype A] [Fintype B] (R : A → B → Prop) :
    2*(∑ a : A, (row R a).card.choose 2) =
      ∑ p ∈ (univ : Finset B).offDiag, codegree R p.1 p.2 := by
  classical
  let I : A → B × B → Prop := fun a p => R a p.1 ∧ R a p.2
  have hrow (a : A) : ((univ : Finset B).offDiag.bipartiteAbove I a) = (row R a).offDiag := by
    ext p
    simp [bipartiteAbove,I,mem_offDiag,mem_row,and_assoc,and_comm]
  have hcol (p : B × B) : ((univ : Finset A).bipartiteBelow I p).card = codegree R p.1 p.2 := by
    simp [bipartiteBelow,I,codegree,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hchoose (a : A) : 2*(row R a).card.choose 2 = (row R a).offDiag.card := by
    rw [offDiag_card]
    exact twice_choose_two _
  calc
    _ = ∑ a : A, (row R a).offDiag.card := by rw [mul_sum]; simp only [hchoose]
    _ = ∑ a : A, ((univ : Finset B).offDiag.bipartiteAbove I a).card := by simp only [hrow]
    _ = ∑ p ∈ (univ : Finset B).offDiag, ((univ : Finset A).bipartiteBelow I p).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow I (s := univ) (t := (univ : Finset B).offDiag)
    _ = _ := by simp only [hcol]

lemma pair_sum_lower [Fintype A] [Fintype B] {R : A → B → Prop} (hh : Heavy R) :
    3*(Fintype.card B).choose 2 ≤ ∑ a : A, (row R a).card.choose 2 := by
  classical
  have hb := sum_le_sum (s := (univ : Finset B).offDiag)
    (fun p hp => hh p.1 p.2 (mem_offDiag.mp hp).2.2)
  rw [← pair_sum_eq_codegrees R] at hb
  simp only [sum_const,Nat.nsmul_eq_mul,offDiag_card,card_univ] at hb
  have hc : 2*(Fintype.card B).choose 2 = Fintype.card B*Fintype.card B-Fintype.card B := by
    exact twice_choose_two _
  omega

/-- Every theta-free triple cover of all column pairs needs at least
choose(k,2) rows. No column-degree bound is needed. -/
theorem rows_lower [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hh : Heavy R) : (Fintype.card B).choose 2 ≤ Fintype.card A := by
  have hu := pair_sum_with_deficit hf hh
  have hl := pair_sum_lower hh
  omega

/-- In the equality case all rows are triples. -/
theorem row_card_of_equality [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hh : Heavy R) (he : Fintype.card A = (Fintype.card B).choose 2)
    (a : A) : (row R a).card = 3 := by
  classical
  have hu := pair_sum_with_deficit hf hh
  have hl := pair_sum_lower hh
  have hlow : (lowRows R).card = 0 := by omega
  have hhigh := high_pairs_le_low_rows hf hh
  have hnlow : ¬ (row R a).card ≤ 2 := by
    intro ha
    have hm : a ∈ lowRows R := by simp [lowRows,ha]
    have hh0 := card_eq_zero.mp hlow
    rw [hh0] at hm
    exact notMem_empty a hm
  have hnhi : ¬ 4 ≤ (row R a).card := by
    intro ha
    have hm : a ∈ highRows R := by simp [highRows,ha]
    have hle := single_le_sum (f := fun b => (row R b).card.choose 2)
      (fun _ _ => Nat.zero_le _) hm
    dsimp only at hle
    rw [hlow] at hhigh
    have hc : 6 ≤ (row R a).card.choose 2 := Nat.choose_le_choose 2 ha
    omega
  omega

/-- Equality also forces every distinct column pair to have exactly
three supporting rows. -/
theorem codegree_of_equality [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hh : Heavy R) (he : Fintype.card A = (Fintype.card B).choose 2)
    (x y : B) (hxy : x ≠ y) : codegree R x y = 3 := by
  classical
  have hpairs : (∑ a : A, (row R a).card.choose 2) = 3*Fintype.card A := by
    simp only [row_card_of_equality hf hh he]
    norm_num [Nat.mul_comm]
  have hsum : (∑ p ∈ (univ : Finset B).offDiag, (3 : ℕ)) =
      ∑ p ∈ (univ : Finset B).offDiag, codegree R p.1 p.2 := by
    rw [← pair_sum_eq_codegrees R,hpairs,he]
    simp only [sum_const,Nat.nsmul_eq_mul,offDiag_card,card_univ]
    have hc := twice_choose_two (Fintype.card B)
    omega
  have hpoint := (sum_eq_sum_iff_of_le (fun p hp =>
    hh p.1 p.2 (mem_offDiag.mp hp).2.2)).mp hsum (x,y)
      (mem_offDiag.mpr ⟨mem_univ _,mem_univ _,hxy⟩)
  exact hpoint.symm

/-- Any heavy clique of columns has the same quadratic row cost. -/
theorem heavy_subset_bound [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (S : Finset B)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 3 ≤ codegree R x y) :
    S.card.choose 2 ≤ Fintype.card A := by
  classical
  let Q : A → S → Prop := fun a b => R a b.val
  have hQ : ¬ HasTheta Q := by
    rintro ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩
    exact hf ⟨a,fun i => (b i).val,ha,Subtype.val_injective.comp hb,
      h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hh : Heavy Q := by
    intro x y hxy
    exact hS x.val x.property y.val y.property (fun he => hxy (Subtype.ext he))
  simpa only [Fintype.card_coe] using rows_lower hQ hh

#print axioms rows_lower
#print axioms row_card_of_equality
#print axioms codegree_of_equality
#print axioms heavy_subset_bound
end Erdos713ThetaHeavyRowCount
