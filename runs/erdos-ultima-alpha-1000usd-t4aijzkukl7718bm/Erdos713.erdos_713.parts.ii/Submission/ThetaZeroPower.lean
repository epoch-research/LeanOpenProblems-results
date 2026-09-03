import FormalConjecturesUtil
import Submission.ThetaWitnessMoments
import Submission.ThetaZeroPairs

/-! A higher power inequality charging only pairs with codegree zero. -/
open Finset
namespace Erdos713ThetaZeroPower
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaAnchorPacking Erdos713ThetaAllWitnessPacking
open Erdos713ThetaWitnessMoments Erdos713ThetaZeroPairs
variable {A B : Type*}
set_option maxHeartbeats 2000000

open scoped Classical in
theorem pruned_zero_sixth_power [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (r D : ℕ) (hr : 6 ≤ r)
    (hD : ∀ x, Nat.card {a // R a x} ≤ D)
    (havg : 20*Fintype.card A*r ≤ ∑ a : A, (row R a).card)
    (hpairs : 16*(Fintype.card B)^2 ≤ r*(∑ a : A, (row R a).card)) :
    r^4*(∑ a : A, (row R a).card)^2 ≤ 1536*D*(zeroSet R).card*(Fintype.card B)^2 := by
  classical
  let m := Fintype.card A
  let e := ∑ a : A, (row R a).card
  let S := (univ : Finset A).filter (fun a => r ≤ (row R a).card)
  let eh := ∑ a ∈ S, (row R a).card
  let Q := ∑ a ∈ S, (row R a).offDiag.card
  let M := ∑ a ∈ S, (witnesses R S a).card
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
  have hRE : r*e ≤ 2*Q+m*r^2 := by
    have hh := Nat.mul_le_mul_left r hE
    nlinarith only [hh,hQr]

  have hQE : r*e ≤ 4*Q := by
    have ha : 20*m*r ≤ e := havg
    have hh := Nat.mul_le_mul_left r ha
    nlinarith only [hRE,hh]
  have hlarge : 4*(Fintype.card B)^2 ≤ Q := by
    have hp : 16*(Fintype.card B)^2 ≤ r*e := hpairs
    omega
  have hQsquare : Q^2 ≤ 4*(Fintype.card B)^2*M := second_moment_lower R S hlarge
  have htot : (r-3)^2*M ≤ 6*D*(zeroSet R).card := by
    have ht := total_all_zero_bound hf S r D hmin hD
    apply le_trans _ ht
    dsimp only [M]
    rw [mul_sum]
    apply sum_le_sum
    intro a ha
    have hh := Nat.sub_le_sub_right (hmin a ha) 3
    have hm := Nat.mul_le_mul_left ((witnesses R S a).card*(r-3)) hh
    nlinarith only [hm]
  have hsquare : r^2 ≤ 4*(r-3)^2 := by
    have hr' : r-3+3 = r := Nat.sub_add_cancel (by omega)
    nlinarith
  have hMsquare : r^2*M ≤ 24*D*(zeroSet R).card := by
    have hh := Nat.mul_le_mul_right M hsquare
    nlinarith only [hh,htot]

  have hEsq := Nat.pow_le_pow_left hQE 2
  change r^4*e^2 ≤ _
  calc
    _ = r^2*(r*e)^2 := by ring
    _ ≤ r^2*(4*Q)^2 := Nat.mul_le_mul_left _ hEsq
    _ = 16*r^2*Q^2 := by ring
    _ ≤ 16*r^2*(4*(Fintype.card B)^2*M) := Nat.mul_le_mul_left _ hQsquare
    _ = 64*(Fintype.card B)^2*(r^2*M) := by ring
    _ ≤ 64*(Fintype.card B)^2*(24*D*(zeroSet R).card) := Nat.mul_le_mul_left _ hMsquare
    _ = _ := by ring

#print axioms pruned_zero_sixth_power
end Erdos713ThetaZeroPower
