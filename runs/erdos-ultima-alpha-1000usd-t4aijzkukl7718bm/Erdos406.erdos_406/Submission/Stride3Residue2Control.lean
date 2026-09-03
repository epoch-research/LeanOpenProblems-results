import Submission.BackwardNFAStrided

namespace Erdos406StrideExport
open Erdos406BackwardStandalone Erdos406BackwardStrided
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 20000

def maskSet (n m : ℕ) : Finset (Fin n) := Finset.univ.filter (fun q => m.testBit q.val)
def stepTable : List (List ℕ) := [[1, 6, 8], [2, 2, 0], [4, 4, 8], [4, 16, 8], [4, 4, 8]]
def relationTable : List (List ℕ) := [[29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 21, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29], [12, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 21, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29], [12, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 21, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29], [12, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29], [28, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 21, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29]]
def data : Data (Fin 5) where
  step q d := maskSet 5 ((stepTable.getD q.val []).getD d 0)
  start := {0}
  accept := maskSet 5 14
  relation p c := maskSet 5 ((relationTable.getD p.val []).getD c 0)

lemma checked_init : ∀ c, c < 64 → ∀ p ∈ data.evalStates c,
    (data.start ∩ data.relation p c).Nonempty := by decide +kernel
lemma checked_step : ∀ p d, d < 3 → ∀ c', c' < 64 →
    ∀ r ∈ data.step p ((64 * d + c') % 3),
    ∀ q ∈ data.relation p ((64 * d + c') / 3),
    (data.step q d ∩ data.relation r c').Nonempty := by decide +kernel
lemma checked_finish : ∀ p ∈ data.accept, data.relation p 0 ⊆ data.accept := by decide +kernel
lemma checked_first : (1 : Fin 5) ∈ data.stepStates data.start 1 := by decide +kernel
lemma checked_loop : ∀ d, d < 2 → (1 : Fin 5) ∈ data.step 1 d := by decide +kernel
lemma checked_accept : (1 : Fin 5) ∈ data.accept := by decide +kernel
lemma checked_seed : Disjoint (data.evalStates (4 ^ 8)) data.accept := by decide +kernel

def simulation := checkedSimulation data 64 (by decide) checked_init checked_step checked_finish

theorem backward (n : ℕ) : acceptsNat data.toNFA (64 * n) → acceptsNat data.toNFA n :=
  simulation.backward n

theorem covers (n : ℕ) (hn : 0 < n) (hg : Nat.digits 3 n ⊆ [0, 1]) :
    acceptsNat data.toNFA n := by
  apply covers_positive_good data.toNFA 1 _ checked_loop checked_accept n hn hg
  change (1 : Fin 5) ∈ data.toNFA.stepSet (data.start : Set (Fin 5)) 1
  rw [← data.stepStates_coe]
  exact checked_first

theorem rejected_seed : ¬ acceptsNat data.toNFA (4 ^ 8) := by
  rintro ⟨p, hp, ha⟩
  rw [← data.evalStates_coe] at hp
  exact Finset.disjoint_left.mp checked_seed hp ha

/-- This excludes ONE exponent class, not all sufficiently large exponents. -/
theorem excludes (j : ℕ) : ¬ Nat.digits 3 (4 ^ (8 + 3 * j)) ⊆ [0, 1] := by
  intro hg
  have hn := simulation.rejects_mul_orbit (4 ^ 8) rejected_seed j
  apply hn
  have he : (64 : ℕ) ^ j * 4 ^ 8 = 4 ^ (8 + 3 * j) := by
    rw [show (64 : ℕ) = 4 ^ 3 by decide, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [he]
  exact covers _ (by positivity) hg

#print axioms excludes
end Erdos406StrideExport
