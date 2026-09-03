import FormalConjecturesUtil
import Submission.ThetaAnchorPacking

/-! An anchor budget after removing low-degree rows. -/
open Finset
namespace Erdos713ThetaAnchorBudget
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaOverlap Erdos713ThetaAnchorPacking
variable {A B : Type*}
set_option maxHeartbeats 2000000

open scoped Classical in
lemma commonRows_split [Fintype A] [Fintype B] (R : A → B → Prop)
    (S : Finset A) (p : B × B) :
    codegree R p.1 p.2 = (commonRows R S p).card + (commonRows R (univ \ S) p).card := by
  classical
  have hu : commonRows R S p ∪ commonRows R (univ \ S) p =
      (univ : Finset A).filter (fun a => R a p.1 ∧ R a p.2) := by
    ext a
    simp only [commonRows,mem_union,mem_filter,mem_sdiff,mem_univ,true_and]
    tauto
  have hd : Disjoint (commonRows R S p) (commonRows R (univ \ S) p) := by
    apply disjoint_left.mpr
    intro a ha hb
    exact (mem_sdiff.mp (mem_filter.mp hb).1).2 (mem_filter.mp ha).1
  have hc := card_union_of_disjoint hd
  rw [hu] at hc
  simpa only [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype] using hc

open scoped Classical in
lemma pair_incidence_sum [Fintype A] [Fintype B] (R : A → B → Prop) (S : Finset A) :
    (∑ a ∈ S, (row R a).offDiag.card) =
      ∑ p ∈ (univ : Finset B).offDiag, (commonRows R S p).card := by
  classical
  let Inc : A → (B × B) → Prop := fun a p => R a p.1 ∧ R a p.2
  have ha (a : A) : ((univ : Finset B).offDiag).bipartiteAbove Inc a = (row R a).offDiag := by
    ext p
    simp only [bipartiteAbove,mem_filter,mem_offDiag,mem_univ,true_and,Inc,mem_row]
    tauto
  have hb (p : B × B) : S.bipartiteBelow Inc p = commonRows R S p := rfl
  calc
    _ = ∑ a ∈ S, (((univ : Finset B).offDiag).bipartiteAbove Inc a).card := by simp only [ha]
    _ = ∑ p ∈ (univ : Finset B).offDiag, (S.bipartiteBelow Inc p).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Inc
    _ = _ := by simp only [hb]

open scoped Classical in
lemma anchor_incidence_sum [Fintype A] [Fintype B] (R : A → B → Prop) (S : Finset A) :
    (∑ a ∈ S, (anchors R S a).card) =
      ∑ p ∈ (univ : Finset B).offDiag,
        if 3 ≤ (commonRows R S p).card then (commonRows R S p).card else 0 := by
  classical
  let Inc : A → (B × B) → Prop := fun a p =>
    R a p.1 ∧ R a p.2 ∧ 3 ≤ (commonRows R S p).card
  have ha (a : A) : ((univ : Finset B).offDiag).bipartiteAbove Inc a = anchors R S a := by
    ext p
    simp only [bipartiteAbove,anchors,mem_filter,mem_offDiag,mem_univ,true_and,Inc,mem_row]
    tauto
  have hb (p : B × B) : (S.bipartiteBelow Inc p).card =
      if 3 ≤ (commonRows R S p).card then (commonRows R S p).card else 0 := by
    by_cases hp : 3 ≤ (commonRows R S p).card
    · simp only [bipartiteBelow,Inc,hp,and_true,if_true]
      rfl
    · simp [bipartiteBelow,Inc,hp]
  calc
    _ = ∑ a ∈ S, (((univ : Finset B).offDiag).bipartiteAbove Inc a).card := by simp only [ha]
    _ = ∑ p ∈ (univ : Finset B).offDiag, (S.bipartiteBelow Inc p).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Inc
    _ = _ := by simp only [hb]

open scoped Classical in
/-- A pair which ceases to be heavy after pruning either was already light
or was supported by a deleted row. Each such pair contributes at most two
incidences to the retained rows. -/
theorem bad_anchor_budget [Fintype A] [Fintype B] (R : A → B → Prop) (S : Finset A) :
    (∑ a ∈ S, (row R a).offDiag.card) ≤
      (∑ a ∈ S, (anchors R S a).card) + 2*lightCount R +
        2*(∑ a ∈ univ \ S, (row R a).offDiag.card) := by
  classical
  have hp (p : B × B) :
      (commonRows R S p).card ≤
        (if 3 ≤ (commonRows R S p).card then (commonRows R S p).card else 0) +
        (if codegree R p.1 p.2 ≤ 2 then 2 else 0) +
        2*(commonRows R (univ \ S) p).card := by
    have hs := commonRows_split R S p
    split_ifs <;> omega
  have hlight : (∑ p ∈ (univ : Finset B).offDiag,
      if codegree R p.1 p.2 ≤ 2 then 2 else 0) ≤ 2*lightCount R := by
    calc
      _ ≤ ∑ p : B × B, if codegree R p.1 p.2 ≤ 2 then 2 else 0 :=
        sum_le_sum_of_subset (subset_univ _)
      _ = 2*lightCount R := by
        rw [← sum_filter]
        change (∑ _p ∈ lightSet R, 2) = 2*lightCount R
        simp [lightSet_card,Nat.mul_comm]
  rw [pair_incidence_sum,anchor_incidence_sum,pair_incidence_sum R (univ \ S)]
  have hh := sum_le_sum (s := (univ : Finset B).offDiag) (fun p _ => hp p)
  simp only [sum_add_distrib,← mul_sum] at hh
  omega

#print axioms commonRows_split
#print axioms pair_incidence_sum
#print axioms anchor_incidence_sum
#print axioms bad_anchor_budget
end Erdos713ThetaAnchorBudget
