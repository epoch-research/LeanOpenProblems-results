import FormalConjecturesUtil
import Submission.RestrictedMoments

/-! A stationary finite-state extension of the subcritical-moment obstruction.
This concerns explicitly defined mass partitions, not the actual prime-factor
sequence, and does not disprove Erdős 371. -/

namespace Erdos371StationaryMomentObstruction

open Finset Erdos371RestrictedMoments

abbrev π (i : State) : ℚ := (base i : ℚ) / 120
abbrev transition (i j : State) : ℚ := (weight i j : ℚ) / (120 * (base i : ℚ))
abbrev observable (u : List ℕ) (i : State) : ℚ := (feature u i : ℚ)
def expectation (f : State → ℚ) : ℚ := ∑ i, π i * f i

lemma pi_pos : ∀ i : State, 0 < π i := by decide +kernel
lemma pi_sum : (∑ i : State, π i) = 1 := by decide +kernel
lemma transition_pos : ∀ i j : State, 0 < transition i j := by decide +kernel
lemma row_sum : ∀ i : State, (∑ j : State, transition i j) = 1 := by decide +kernel
lemma stationary : ∀ j : State, (∑ i : State, π i * transition i j) = π j := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma low_forward : ∀ u ∈ selections, u.sum ≤ 2 → ∀ i : State,
    (∑ j : State, transition i j * observable u j) = expectation (observable u) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma low_backward : ∀ u ∈ selections, u.sum ≤ 2 → ∀ j : State,
    (∑ i : State, π i * observable u i * transition i j) =
      π j * expectation (observable u) := by
  decide +kernel

/-- The conditional product moment of successive observations. -/
def eval : List (List ℕ) → State → ℚ
  | [], _ => 1
  | u :: us, i => observable u i * ∑ j : State, transition i j * eval us j

def moment (us : List (List ℕ)) : ℚ := expectation (eval us)
def independentMoment (us : List (List ℕ)) : ℚ :=
  (us.map (fun u => expectation (observable u))).prod

lemma moment_nil : moment [] = 1 := by
  simpa [moment, expectation, eval] using pi_sum

lemma independentMoment_nil : independentMoment [] = 1 := rfl
lemma independentMoment_cons (u : List ℕ) (us : List (List ℕ)) :
    independentMoment (u :: us) = expectation (observable u) * independentMoment us := rfl

lemma moment_cons_low {u : List ℕ} (hu : u ∈ selections) (hsmall : u.sum ≤ 2)
    (us : List (List ℕ)) :
    moment (u :: us) = expectation (observable u) * moment us := by
  unfold moment expectation
  simp only [eval, ← mul_assoc, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j : State, (∑ i : State, π i * observable u i * transition i j) * eval us j := by
      simp only [Finset.sum_mul]
    _ = ∑ j : State, (π j * expectation (observable u)) * eval us j := by
      simp_rw [low_backward u hu hsmall]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      unfold expectation
      ring

lemma transition_eval_low (us : List (List ℕ))
    (h : ∀ u ∈ us, u ∈ selections ∧ u.sum ≤ 2) (i : State) :
    (∑ j : State, transition i j * eval us j) = independentMoment us := by
  induction us generalizing i with
  | nil => simpa [eval, independentMoment] using row_sum i
  | cons u us ih =>
      have hu := h u (by simp)
      have ht : ∀ v ∈ us, v ∈ selections ∧ v.sum ≤ 2 := fun v hv => h v (by simp [hv])
      simp only [eval]
      simp_rw [ih ht]
      simp only [← mul_assoc]
      rw [← Finset.sum_mul]
      rw [low_forward u hu.1 hu.2 i, independentMoment_cons]

lemma moment_cons_low_tail (u : List ℕ) (us : List (List ℕ))
    (h : ∀ v ∈ us, v ∈ selections ∧ v.sum ≤ 2) :
    moment (u :: us) = expectation (observable u) * independentMoment us := by
  unfold moment expectation
  simp only [eval]
  simp_rw [transition_eval_low us h]
  simp only [Finset.sum_mul, mul_assoc]

/-- All finite joint selection moments of total mass at most five are those
of independent copies, despite the biased adjacent largest-part comparison. -/
theorem subcritical_path_moments (us : List (List ℕ))
    (hmem : ∀ u ∈ us, u ∈ selections) (hbudget : (us.map List.sum).sum ≤ 5) :
    moment us = independentMoment us := by
  induction us with
  | nil => exact moment_nil
  | cons u us ih =>
      have hu := hmem u (by simp)
      have ht : ∀ v ∈ us, v ∈ selections := fun v hv => hmem v (by simp [hv])
      have hb : u.sum + (us.map List.sum).sum ≤ 5 := by simpa using hbudget
      by_cases hsmall : u.sum ≤ 2
      · rw [moment_cons_low hu hsmall, ih ht (by omega), independentMoment_cons]
      · have htail : ∀ v ∈ us, v ∈ selections ∧ v.sum ≤ 2 := by
          intro v hv
          refine ⟨ht v hv, ?_⟩
          have hvle : v.sum ≤ (us.map List.sum).sum :=
            List.le_sum_of_mem (List.mem_map.mpr ⟨v,hv,rfl⟩)
          omega
        exact moment_cons_low_tail u us htail

/-- The stationary adjacent signed comparison is strictly positive. -/
lemma signed_adjacent_mean :
    (∑ i : State, ∑ j : State, π i * transition i j *
      (if largest i > largest j then (1:ℚ) else if largest i < largest j then -1 else 0)) =
      1 / 7200 := by
  decide +kernel

lemma not_reversible : ¬ ∀ i j : State, π i * transition i j = π j * transition j i := by
  decide +kernel

end Erdos371StationaryMomentObstruction

#print axioms Erdos371StationaryMomentObstruction.subcritical_path_moments
#print axioms Erdos371StationaryMomentObstruction.signed_adjacent_mean
