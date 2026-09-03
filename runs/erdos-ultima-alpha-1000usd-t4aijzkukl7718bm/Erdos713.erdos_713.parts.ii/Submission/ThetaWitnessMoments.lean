import FormalConjecturesUtil
import Submission.ThetaAllWitnessPacking
import Submission.ThetaAnchorBudget

/-! Second moments of retained heavy-pair books. -/
open Finset
namespace Erdos713ThetaWitnessMoments
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaOverlap Erdos713ThetaAnchorPacking
open Erdos713ThetaAllWitnessPacking Erdos713ThetaAnchorBudget
variable {A B : Type*}
set_option maxHeartbeats 2000000

open scoped Classical in
/-- Summing the root packing bound costs only ONE column degree per
ordered light pair, not its product with the other column degree. -/
theorem total_all_bound [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (S : Finset A) (r D : ℕ)
    (hmin : ∀ b ∈ S, r ≤ (row R b).card)
    (hD : ∀ x, Nat.card {a // R a x} ≤ D) :
    (∑ a ∈ S, (witnesses R S a).card*((row R a).card-3)*(r-3)) ≤
      6*D*lightCount R := by
  classical
  have hs : (∑ a ∈ S, (lightAt R a).card) ≤ D*lightCount R := by
    let Inc : A → (B × B) → Prop := fun a p => R a p.1
    have ha (a : A) : (lightSet R).bipartiteAbove Inc a = lightAt R a := rfl
    have hb (p : B × B) : (S.bipartiteBelow Inc p).card ≤ D := by
      have hsub : S.bipartiteBelow Inc p ⊆ (univ : Finset A).filter (fun a => R a p.1) := by
        intro a ha
        exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ha).2⟩
      apply (card_le_card hsub).trans
      simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using hD p.1
    calc
      _ = ∑ a ∈ S, ((lightSet R).bipartiteAbove Inc a).card := by simp only [ha]
      _ = ∑ p ∈ lightSet R, (S.bipartiteBelow Inc p).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Inc
      _ ≤ ∑ _p ∈ lightSet R, D := sum_le_sum (fun p _ => hb p)
      _ = _ := by simp [lightSet_card,Nat.mul_comm]
  calc
    _ ≤ ∑ a ∈ S, 6*(lightAt R a).card := sum_le_sum (fun a ha => root_all_bound hf S r hmin a ha)
    _ = 6*(∑ a ∈ S, (lightAt R a).card) := by rw [mul_sum]
    _ ≤ 6*(D*lightCount R) := Nat.mul_le_mul_left 6 hs
    _ = _ := by ring

open scoped Classical in
lemma weighted_anchor_sum [Fintype A] [Fintype B] (R : A → B → Prop)
    (S : Finset A) (w : B × B → ℕ) :
    (∑ a ∈ S, ∑ p ∈ anchors R S a, w p) =
      ∑ p ∈ (univ : Finset B).offDiag,
        if 3 ≤ (commonRows R S p).card then (commonRows R S p).card*w p else 0 := by
  classical
  have he (a : A) : anchors R S a = ((univ : Finset B).offDiag).filter
      (fun p => R a p.1 ∧ R a p.2 ∧ 3 ≤ (commonRows R S p).card) := by
    ext p
    simp only [anchors,mem_filter,mem_offDiag,mem_univ,true_and,mem_row]
    tauto
  simp_rw [he,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  by_cases hc : 3 ≤ (commonRows R S p).card
  · simp only [hc,and_true,if_true]
    rw [← sum_filter]
    change (∑ _a ∈ commonRows R S p, w p) = _
    simp
  · simp [hc]

open scoped Classical in
lemma witness_incidence_sum [Fintype A] [Fintype B] (R : A → B → Prop) (S : Finset A) :
    (∑ a ∈ S, (witnesses R S a).card) =
      ∑ p ∈ (univ : Finset B).offDiag,
        if 3 ≤ (commonRows R S p).card then
          (commonRows R S p).card*((commonRows R S p).card-1) else 0 := by
  classical
  calc
    _ = ∑ a ∈ S, ∑ p ∈ anchors R S a, ((commonRows R S p).card-1) := by
      apply sum_congr rfl
      intro a ha
      exact witnesses_card R S a ha
    _ = _ := weighted_anchor_sum R S (fun p => (commonRows R S p).card-1)

lemma square_bound (c : ℕ) : c^2 ≤ 2*(if 3 ≤ c then c*(c-1) else 0)+4 := by
  by_cases hc : 3 ≤ c
  · rw [if_pos hc]
    have hsub : c-1+1 = c := Nat.sub_add_cancel (by omega)
    nlinarith
  · rw [if_neg hc]
    interval_cases c <;> decide

open scoped Classical in
/-- When the first pair moment is large, it forces many retained witnesses. -/
theorem second_moment_lower [Fintype A] [Fintype B] (R : A → B → Prop) (S : Finset A)
    (hlarge : 4*(Fintype.card B)^2 ≤ ∑ a ∈ S, (row R a).offDiag.card) :
    (∑ a ∈ S, (row R a).offDiag.card)^2 ≤
      4*(Fintype.card B)^2*(∑ a ∈ S, (witnesses R S a).card) := by
  classical
  let P := (univ : Finset B).offDiag
  let Q := ∑ p ∈ P, (commonRows R S p).card
  let M := ∑ p ∈ P, if 3 ≤ (commonRows R S p).card then
    (commonRows R S p).card*((commonRows R S p).card-1) else 0
  let Z := ∑ p ∈ P, ((commonRows R S p).card)^2
  have hP : P.card ≤ (Fintype.card B)^2 := by
    simp only [P,offDiag_card,card_univ,pow_two]
    omega
  have hc : Q^2 ≤ P.card*Z := by
    simpa only [Q,Z] using
      (sq_sum_le_card_mul_sum_sq (s := P) (f := fun p => (commonRows R S p).card))
  have hZ : Z ≤ 2*M+4*(Fintype.card B)^2 := by
    have hs := sum_le_sum (s := P) (fun p _ => square_bound (commonRows R S p).card)
    simp only [sum_add_distrib,← mul_sum,sum_const,Nat.nsmul_eq_mul] at hs
    dsimp only [Z,M]
    nlinarith only [hs,hP]
  have hQ : 4*(Fintype.card B)^2 ≤ Q := by
    simpa only [pair_incidence_sum,Q,P] using hlarge
  have h1 : Q^2 ≤ (Fintype.card B)^2*(2*M+4*(Fintype.card B)^2) :=
    hc.trans (Nat.mul_le_mul hP hZ)
  have h2 := Nat.pow_le_pow_left hQ 2
  rw [pair_incidence_sum,witness_incidence_sum]
  change Q^2 ≤ 4*(Fintype.card B)^2*M
  nlinarith only [h1,h2]

#print axioms total_all_bound
#print axioms witness_incidence_sum
#print axioms second_moment_lower
end Erdos713ThetaWitnessMoments
