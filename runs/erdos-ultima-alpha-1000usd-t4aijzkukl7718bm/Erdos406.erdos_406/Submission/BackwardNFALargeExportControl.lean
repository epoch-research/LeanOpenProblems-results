import Submission.BackwardNFAFinite

/-! Generated finite backward-simulation checks; auxiliary file, not Spec.lean. -/
namespace Erdos406BackwardExport
open Erdos406BackwardNFAFinite Erdos406ComplementNFA

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 20000

def maskSet (n m : ℕ) : Finset (Fin n) := Finset.univ.filter (fun q => m.testBit q.val)

def stepTable : List (List ℕ) := [[1, 6, 4], [2, 2, 0], [4, 4, 4], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]

def relationTable : List (List ℕ) := [[5, 5, 5, 5], [4, 5, 5, 5], [4, 5, 5, 5], [65535, 65535, 65535, 65535], [65535, 65535, 65535, 65535], [65535, 65535, 65535, 65535], [65535, 65535, 65535, 65535], [65535, 65535, 65535, 65535], [65535, 65535, 65535, 65535], [65535, 65535, 65535, 65535], [65535, 65535, 65535, 65535], [65535, 65535, 65535, 65535], [65535, 65535, 65535, 65535], [65535, 65535, 65535, 65535], [65535, 65535, 65535, 65535], [65535, 65535, 65535, 65535]]

def data : Data (Fin 16) where
  step q d := maskSet 16 ((stepTable.getD q.val []).getD d 0)
  start := {0}
  accept := maskSet 16 6
  relation p c := maskSet 16 ((relationTable.getD p.val []).getD c 0)

lemma checked_init : ∀ c, c < 4 → ∀ p ∈ data.evalStates c,
    (data.start ∩ data.relation p c).Nonempty := by decide +kernel

lemma checked_step : ∀ p d, d < 3 → ∀ c', c' < 4 →
    ∀ r ∈ data.step p ((4 * d + c') % 3),
    ∀ q ∈ data.relation p ((4 * d + c') / 3),
    (data.step q d ∩ data.relation r c').Nonempty := by decide +kernel

lemma checked_finish : ∀ p ∈ data.accept, data.relation p 0 ⊆ data.accept := by
  decide +kernel

lemma checked_first : (1 : Fin 16) ∈ data.stepStates data.start 1 := by decide +kernel
lemma checked_loop : ∀ d, d < 2 → (1 : Fin 16) ∈ data.step 1 d := by decide +kernel
lemma checked_accept : (1 : Fin 16) ∈ data.accept := by decide +kernel

 theorem backward (n : ℕ) : acceptsNat data.toNFA (4 * n) → acceptsNat data.toNFA n :=
  (data.toSimulation_fast checked_init checked_step checked_finish).backward n

 theorem covers (n : ℕ) (hn : 0 < n) (hg : Nat.digits 3 n ⊆ [0, 1]) :
    acceptsNat data.toNFA n := by
  apply covers_positive_good data.toNFA 1 _ checked_loop checked_accept n hn hg
  change (1 : Fin 16) ∈ data.toNFA.stepSet (data.start : Set (Fin 16)) 1
  rw [← data.stepStates_coe]
  exact checked_first

/- Control only: no rejected seed or finiteness result. -/

#print axioms backward
#print axioms covers
end Erdos406BackwardExport
