import FormalConjecturesUtil
import Submission.ThetaPositiveCompletion
import Submission.ThetaRigidNormalization
import Submission.ThetaDensityGapReduction

/-! An equivalence of two UNPROVED auxiliary density-gap assertions.
The normalized version has rigid intersections and no positive light pairs.
Neither assertion is established, and Erdős 713 remains unresolved. -/
open Finset
open scoped Classical
namespace Erdos713ThetaCompletedGapReduction
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross (lightCount)
open Erdos713ThetaRowRestriction Erdos713ThetaRigidNormalization
open Erdos713ThetaPositiveCompletion Erdos713ThetaDensityGapReduction
set_option maxHeartbeats 2000000

/-- Rows of degree at most three can be discarded at a cost of at most
nine times the original row count in the ordered light-pair budget. -/
theorem discard_small {A B : Type*} [Fintype A] [Fintype B] (R : A → B → Prop) :
    ∃ S : Finset A,
      (∀ a : S, 4 ≤ (row (restrict R S) a).card) ∧
      lightCount (restrict R S) ≤ lightCount R+9*Nat.card A := by
  let S := (univ : Finset A).filter (fun a => 4 ≤ (row R a).card)
  have hlow (a : A) (ha : a ∈ univ \ S) : (row R a).card ≤ 3 := by
    have hh := (mem_sdiff.mp ha).2
    have hn : ¬ 4 ≤ (row R a).card := by simpa [S] using hh
    omega
  have hs : (∑ a ∈ univ \ S, (row R a).card^2) ≤ 9*Nat.card A := by
    calc
      _ ≤ ∑ _a ∈ univ \ S, 9 := sum_le_sum (fun a ha => by
        have hh := Nat.pow_le_pow_left (hlow a ha) 2
        simpa using hh)
      _ = 9*(univ \ S).card := by simp [mul_comm]
      _ ≤ 9*Nat.card A := Nat.mul_le_mul_left 9 (by simpa only [Nat.card_eq_fintype_card] using card_le_univ (univ \ S))
  refine ⟨S,fun a => (mem_filter.mp a.property).2,?_⟩
  exact (light_restrict_le R S).trans (Nat.add_le_add_left hs _)

/-- A completed-case constant would yield a general constant. It is not
asserted that such a completed-case constant exists. -/
theorem densityGap_of_completed {C : ℕ} (hC : CompletedGap C) : DensityGap (308*C) := by
  intro A B iA iB R hf
  obtain ⟨S,hmin,hlight⟩ := discard_small R
  let L := restrict R S
  have hLf : ¬ HasTheta L := restrict_no_theta hf S
  obtain ⟨D,iD,f,Q,_hfi,hD,_hsub,hQ,_hrows,hr,_hE,hL⟩ :=
    normalize_rigid hLf 2 (by decide) hmin
  have hm : Nat.card D ≤ Nat.card A := by
    have hh := hD.trans (show Fintype.card S ≤ Fintype.card A from by simpa only [Fintype.card_coe] using card_le_univ S)
    simpa only [Nat.card_eq_fintype_card] using hh
  have ht : lightCount Q ≤ 17*(lightCount R+9*Nat.card A) :=
    hL.trans (Nat.mul_le_mul_left 17 hlight)
  have hh := rigid_gap_of_completed hC Q hQ hr
  calc
    _ ≤ 2*C*(Nat.card D+lightCount Q) := hh
    _ ≤ 2*C*(154*(Nat.card A+lightCount R)) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

lemma completed_light_eq_zero {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (hc : ∀ x y, codegree R x y = 0 ∨ 3 ≤ codegree R x y) :
    lightCount R = zeroCount R := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro p
  have hh := hc p.1 p.2
  omega

/-- The general hypothesis immediately includes the normalized case. -/
theorem completed_of_densityGap {C : ℕ} (hC : DensityGap C) : CompletedGap C := by
  intro A B iA iB R hf _hr hc
  have hh := hC A B R hf
  rwa [completed_light_eq_zero R hc] at hh

/-- This is an equivalence of auxiliary existence statements, not a proof
of either side and not a reformulation of the whole Erdős conjecture. -/
theorem exists_constant_iff :
    (∃ C : ℕ, DensityGap C) ↔ ∃ C : ℕ, CompletedGap C := by
  constructor
  · rintro ⟨C,hC⟩
    exact ⟨C,completed_of_densityGap hC⟩
  · rintro ⟨C,hC⟩
    exact ⟨308*C,densityGap_of_completed hC⟩

#print axioms discard_small
#print axioms densityGap_of_completed
#print axioms completed_of_densityGap
#print axioms exists_constant_iff
end Erdos713ThetaCompletedGapReduction
