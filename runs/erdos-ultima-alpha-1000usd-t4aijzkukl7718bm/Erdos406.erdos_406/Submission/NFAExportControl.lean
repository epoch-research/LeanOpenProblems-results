import Submission.NFAFiniteCertificate
import Submission.NFAFiniteLanguageCertificates

/-! Generated auxiliary certificate checks. This file is not Spec.lean. -/
namespace Erdos406Exported
open Erdos406NFAFinite

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 20000

def maskSet (n m : ℕ) : Finset (Fin n) := Finset.univ.filter (fun q => m.testBit q.val)

def stepTable : List (List ℕ) := [[1, 2, 4], [2, 2, 4], [4, 2, 4]]

def familyTable : List (List (List ℕ)) := [[[1], [2], [4], [2]], [[2], [2, 4], [2, 4], [2, 4]], [[4], [2, 4], [2, 4], [2, 4]]]

def data : Data (Fin 3) where
  step q d := maskSet 3 ((stepTable.getD q.val []).getD d 0)
  start := {0}
  accept := maskSet 3 4
  cutoff := 0
  stride := 1
  family q c := (((familyTable.getD q.val []).getD c []).toFinset).image (maskSet 3)

lemma stride_pos : 0 < data.stride := by decide +kernel

lemma checked_init : ∀ q ∈ data.start, ∀ c, c < 4 ^ data.stride →
    ∃ U ∈ data.family q c, U ⊆ data.evalStates c := by
  decide +kernel

lemma checked_step : ∀ q c, c < 4 ^ data.stride → ∀ U ∈ data.family q c,
    ∀ d, d < 3 → ∀ e, e < 3 → ∀ c', c' < 4 ^ data.stride →
    4 ^ data.stride * d + c' = 3 * c + e → ∀ r ∈ data.step q d,
    ∃ V ∈ data.family r c', V ⊆ data.stepStates U e := by
  decide +kernel

lemma checked_finish : ∀ q ∈ data.accept, ∀ U ∈ data.family q 0,
    (U ∩ data.accept).Nonempty := by
  decide +kernel

/- The control result below will take the seed as an explicit premise. -/

def goodReachable : Finset (Fin 3) := maskSet 3 2

def coaccessible : Finset (Fin 3) := maskSet 3 4

def rank (q : Fin 3) : ℕ := ([0, 0, 0] : List ℕ).getD q.val 0

lemma checked_startG : data.stepStates data.start 1 ⊆ goodReachable := by decide +kernel
lemma checked_stepG : ∀ q ∈ goodReachable, ∀ d, d < 2 →
    data.step q d ⊆ goodReachable := by decide +kernel
lemma checked_acceptK : data.accept ⊆ coaccessible := by decide +kernel
lemma checked_backK : ∀ q d, d < 2 → ∀ r, r ∈ data.step q d →
    r ∈ coaccessible → q ∈ coaccessible := by decide +kernel
lemma checked_rank : ∀ q d, d < 2 → ∀ r, q ∈ goodReachable → r ∈ coaccessible →
    r ∈ data.step q d → rank r < rank q := by decide +kernel

theorem conditional_result (checked_seed : ∀ r, r < data.stride → (data.evalStates (4 ^ (data.cutoff + r)) ∩ data.accept).Nonempty) : {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply Erdos406NFARank.finite_of_rank
    (data.toCore stride_pos checked_init checked_step checked_finish checked_seed)
    (goodReachable : Set (Fin 3)) (coaccessible : Set (Fin 3)) rank
  · change data.toNFA.stepSet (data.start : Set (Fin 3)) 1 ⊆ goodReachable
    rw [← data.stepStates_coe]
    exact checked_startG
  · exact checked_stepG
  · exact checked_acceptK
  · intro q d r hd
    exact checked_backK q d hd r
  · intro q d r hd
    exact checked_rank q d hd r

#print axioms checked_step
#print axioms conditional_result
end Erdos406Exported

namespace Erdos406Exported
/-- The control language does not accept the required power-of-four seed. -/
lemma checked_seed_fails : ¬ ∀ r, r < data.stride →
    (data.evalStates (4 ^ (data.cutoff + r)) ∩ data.accept).Nonempty := by
  decide +kernel
#print axioms checked_seed_fails
#check conditional_result
end Erdos406Exported
