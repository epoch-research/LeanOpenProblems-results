import Submission.BinaryResidueSplitFiniteCheck

/-! Generated binary-residue finite checks. All proofs use kernel reduction. -/
namespace Erdos406BinaryResidueExport
open Erdos406BinaryResidueSplit Erdos406BinaryCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 100000
def stepTable : List (List ℕ) := [[0, 0, 2, 0, 1, 2, 1, 0], [0, 0, 3, 1, 0, 3, 2, 3], [0, 0, 3, 2, 0, 2, 1, 0], [0, 0, 1, 3, 3, 2, 3, 0], [0, 0, 2, 3, 2, 3, 3, 0], [0, 0, 3, 2, 3, 2, 2, 3], [0, 0, 0, 2, 0, 1, 1, 0], [0, 0, 1, 3, 1, 3, 2, 3], [0, 0, 3, 2, 1, 2, 3, 3], [0, 0, 3, 3, 1, 0, 3, 2], [0, 0, 0, 0, 2, 2, 2, 0], [0, 0, 1, 0, 3, 3, 3, 1], [0, 0, 3, 0, 0, 0, 1, 1], [0, 3, 2, 3, 2, 2, 0, 0], [3, 2, 0, 2, 1, 2, 2, 2], [2, 2, 0, 0, 1, 1, 0, 1], [0, 2, 2, 3, 1, 0, 1, 0], [0, 0, 3, 3, 1, 3, 3, 2], [3, 0, 1, 1, 3, 3, 3, 1], [1, 0, 0, 2, 0, 3, 2, 0], [1, 0, 3, 2, 1, 2, 1, 1], [3, 2, 2, 0, 0, 0, 3, 2], [0, 2, 3, 1, 1, 3, 3, 1], [2, 0, 0, 2, 0, 3, 0, 0], [1, 1, 1, 3, 3, 3, 1, 3], [1, 2, 0, 0, 2, 3, 3, 3], [0, 3, 1, 3, 3, 3, 2, 1]]
def relationTable : List (List ℕ) := [[1, 2, 12, 12, 1, 5, 11, 11, 1, 13, 5, 4], [11, 7, 11, 7, 3, 6, 1, 6, 7, 7, 5, 7], [11, 0, 15, 11, 9, 0, 15, 13, 5, 0, 13, 4], [11, 8, 10, 9, 11, 11, 10, 9, 7, 5, 3, 5], [3, 11, 9, 0, 7, 7, 2, 0, 7, 7, 7, 0], [13, 12, 13, 0, 7, 5, 15, 0, 13, 9, 13, 0], [15, 8, 6, 11, 13, 4, 5, 13, 13, 5, 13, 13], [11, 10, 1, 3, 11, 10, 3, 11, 15, 15, 1, 15], [13, 0, 15, 13, 15, 0, 15, 6, 15, 0, 15, 10], [12, 2, 0, 14, 11, 5, 0, 15, 4, 13, 0, 13], [15, 11, 0, 15, 7, 3, 0, 7, 7, 5, 0, 7], [15, 11, 13, 0, 15, 13, 11, 0, 13, 5, 13, 0], [11, 10, 0, 9, 11, 3, 0, 9, 7, 7, 0, 5], [9, 11, 8, 0, 2, 7, 2, 0, 7, 7, 5, 0], [13, 12, 13, 0, 15, 7, 7, 0, 13, 13, 13, 0], [6, 0, 8, 15, 5, 0, 12, 13, 13, 0, 5, 13], [11, 10, 1, 10, 11, 10, 11, 10, 15, 15, 9, 5], [13, 0, 13, 11, 15, 0, 15, 7, 15, 0, 10, 15], [2, 12, 12, 6, 5, 11, 11, 5, 13, 4, 4, 13], [15, 0, 15, 9, 7, 0, 7, 3, 7, 0, 7, 5], [15, 0, 15, 5, 15, 0, 13, 8, 13, 0, 5, 4], [9, 10, 0, 10, 9, 11, 0, 10, 5, 7, 0, 3], [3, 11, 0, 11, 7, 7, 0, 3, 7, 7, 0, 7], [13, 12, 12, 13, 15, 5, 5, 11, 13, 9, 8, 13], [15, 9, 6, 10, 13, 5, 5, 13, 13, 5, 5, 5], [3, 11, 10, 2, 11, 11, 10, 10, 11, 13, 11, 3], [3, 13, 11, 13, 3, 4, 3, 11, 4, 2, 5, 8]]
def acceptTable : List ℕ := [15, 15, 0, 15, 15, 0, 0, 0, 0, 15, 15, 0, 15, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def tailTable : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def data : Data 27 4 where
  step r a d := rem 4 (by decide) ((stepTable.getD r.val []).getD (2 * a.val + d.val) 0)
  test r a := (acceptTable.getD r.val 0).testBit a.val
  relation r a b c := ((relationTable.getD r.val []).getD (4 * c.val + a.val) 0).testBit b.val
  tail r a := (tailTable.getD r.val 0).testBit a.val

lemma checked_start : ∀ c : Fin 3,
    data.relation 0 0 (evalNat (data.dfa (by decide) (by decide)) c.val).2 c = true := by
  decide +kernel
lemma checked_step : ∀ (r : Fin 27) (a b : Fin 4) (c cp : Fin 3) (d e : Fin 2),
    3*d.val+cp.val=2*c.val+e.val → data.relation r a b c = true →
    data.relation (nextParent (by decide) r d.val) (data.step r a d)
      (data.step (outputParent (by decide) r c.val) b e) cp = true := by
  decide +kernel
lemma checked_finish : ∀ (r : Fin 27) (a b : Fin 4) (c : Fin 2),
    data.relation r a b ⟨c.val, by omega⟩ = true → data.test r a = true →
    data.test (outputParent (by decide) r c.val) b = true := by
  decide +kernel
lemma checked_zero : data.test 0 0 = true := by decide +kernel
lemma checked_tail_step : ∀ (r : Fin 27) (a : Fin 4), data.tail r a = true →
    data.tail (nextParent (by decide) r 0) (data.step r a 0) = true := by
  decide +kernel
lemma checked_tail_reject : ∀ (r : Fin 27) (a : Fin 4), data.tail r a = true →
    data.test r a = false := by
  decide +kernel

/-- Control only: the necessary tail seed is FALSE. No finiteness is proved. -/
lemma no_seed : ¬ (data.tail (evalNat (data.dfa (by decide) (by decide)) (2 ^ 40)).1 (evalNat (data.dfa (by decide) (by decide)) (2 ^ 40)).2 = true) := by decide +kernel
#print axioms checked_start
#print axioms checked_step
#print axioms checked_finish
#print axioms checked_zero
#print axioms checked_tail_step
#print axioms checked_tail_reject
end Erdos406BinaryResidueExport
