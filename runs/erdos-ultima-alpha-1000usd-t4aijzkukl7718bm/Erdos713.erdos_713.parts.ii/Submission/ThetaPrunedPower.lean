import FormalConjecturesUtil
import Submission.ThetaAnchorBudget

/-! A finite power inequality from pruning and anchor packing. -/
open Finset
namespace Erdos713ThetaPrunedPower
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaOverlap Erdos713ThetaAnchorPacking
open Erdos713ThetaAnchorBudget
variable {A B : Type*}
set_option maxHeartbeats 2000000

open scoped Classical in
/-- If a threshold is well below the average row degree and its product
with the incidence count dominates the light-pair count, anchor packing
bounds the cube of the threshold times the incidence count. -/
theorem pruned_power [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (r D : ℕ) (hr : 6 ≤ r)
    (hD : ∀ x, Nat.card {a // R a x} ≤ D)
    (havg : 20*Fintype.card A*r ≤ ∑ a : A, (row R a).card)
    (hlight : 16*lightCount R ≤ r*(∑ a : A, (row R a).card)) :
    r^3*(∑ a : A, (row R a).card) ≤ 96*D*lightCount R := by
  classical
  let m := Fintype.card A
  let e := ∑ a : A, (row R a).card
  let S := (univ : Finset A).filter (fun a => r ≤ (row R a).card)
  let eh := ∑ a ∈ S, (row R a).card
  let Q := ∑ a ∈ S, (row R a).offDiag.card
  let M := ∑ a ∈ S, (anchors R S a).card
  have hmin : ∀ a ∈ S, r ≤ (row R a).card := fun a ha => (mem_filter.mp ha).2
  have hlow (a : A) (ha : a ∈ univ \ S) : (row R a).card < r := by
    have hn := (mem_sdiff.mp ha).2
    simpa [S] using hn
  have helow : (∑ a ∈ univ \ S, (row R a).card) ≤ m*r := by
    calc
      _ ≤ ∑ _a ∈ univ \ S, r := sum_le_sum (fun a ha => (hlow a ha).le)
      _ = (univ \ S).card*r := by simp
      _ ≤ m*r := Nat.mul_le_mul_right r (card_le_card (sdiff_subset))
  have hE : e ≤ eh+m*r := by
    have hsplit : e = eh+(∑ a ∈ univ \ S, (row R a).card) := by
      exact (sum_add_sum_compl (s := S) (f := fun a => (row R a).card)).symm
    rw [hsplit]
    exact Nat.add_le_add_left helow eh
  have hprod (a : A) : (row R a).offDiag.card = (row R a).card*((row R a).card-1) := by
    rw [offDiag_card,Nat.mul_sub_left_distrib,Nat.mul_one]
  have hQlow : (∑ a ∈ univ \ S, (row R a).offDiag.card) ≤ m*r^2 := by
    calc
      _ ≤ ∑ _a ∈ univ \ S, r^2 := by
        apply sum_le_sum
        intro a ha
        rw [hprod]
        have h1 := (hlow a ha).le
        have h2 : (row R a).card-1 ≤ r := (Nat.sub_le _ _).trans h1
        simpa only [pow_two] using Nat.mul_le_mul h1 h2
      _ = (univ \ S).card*r^2 := by simp
      _ ≤ m*r^2 := Nat.mul_le_mul_right _ (card_le_card sdiff_subset)
  have hQr : r*eh ≤ 2*Q := by
    dsimp only [eh,Q]
    rw [mul_sum,mul_sum]
    apply sum_le_sum
    intro a ha
    rw [hprod]
    have hd := hmin a ha
    have hd' : r ≤ 2*((row R a).card-1) := by omega
    have hh := Nat.mul_le_mul_right (row R a).card hd'
    nlinarith only [hh]
  have hQM : Q ≤ M+2*lightCount R+2*(m*r^2) := by
    have hh := bad_anchor_budget R S
    exact hh.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hQlow) _)
  have hRE : r*e ≤ 2*Q+m*r^2 := by
    have hh := Nat.mul_le_mul_left r hE
    nlinarith only [hh,hQr]
  have hMr : r*e ≤ 4*M := by
    have ha : 20*m*r ≤ e := havg
    have hb : 16*lightCount R ≤ r*e := hlight
    have hh := Nat.mul_le_mul_left r ha
    nlinarith only [hRE,hQM,hb,hh]
  have htot : (r-3)^2*M ≤ 6*D*lightCount R := by
    have ht := total_anchor_bound hf S r D hmin hD
    apply le_trans _ ht
    dsimp only [M]
    rw [mul_sum]
    apply sum_le_sum
    intro a ha
    have hh := Nat.sub_le_sub_right (hmin a ha) 3
    have hm := Nat.mul_le_mul_left ((anchors R S a).card*(r-3)) hh
    nlinarith only [hm]
  have hsquare : r^2 ≤ 4*(r-3)^2 := by
    have hr' : r-3+3 = r := Nat.sub_add_cancel (by omega)
    nlinarith
  have hMsquare : r^2*M ≤ 24*D*lightCount R := by
    have hh := Nat.mul_le_mul_right M hsquare
    nlinarith only [hh,htot]
  change r^3*e ≤ _
  calc
    r^3*e = r^2*(r*e) := by ring
    _ ≤ r^2*(4*M) := Nat.mul_le_mul_left _ hMr
    _ = 4*(r^2*M) := by ring
    _ ≤ 4*(24*D*lightCount R) := Nat.mul_le_mul_left 4 hMsquare
    _ = _ := by ring

#print axioms pruned_power
end Erdos713ThetaPrunedPower
