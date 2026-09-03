import Submission.BinaryEventualFiniteCheck

/-! Generated eventual binary-residue checks, using kernel reduction. -/
namespace Erdos406BinaryEventualExport
open Erdos406BinaryResidueSplit Erdos406BinaryCertificate Erdos406BinaryEventualFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 100000
def stepTable : List (List ℕ) := [[0, 1, 3, 2, 3, 3, 3, 3]]
def relationTable : List (List (List ℕ)) := [[[0, 4, 0, 0, 0, 8, 0, 0, 0, 8, 0, 0]], [[0, 0, 8, 8, 0, 0, 8, 8, 0, 0, 8, 8]], [[0, 0, 0, 8, 0, 0, 0, 8, 0, 0, 0, 8]]]
def acceptTable : List ℕ := [11]
def tailTable : List ℕ := [0]

def data : Data 1 4 where
  step r a d := rem 4 (by decide) ((stepTable.getD r.val []).getD (2 * a.val + d.val) 0)
  test r a := (acceptTable.getD r.val 0).testBit a.val
  relation _ _ _ _ := false
  tail r a := (tailTable.getD r.val 0).testBit a.val

def rel (h : Fin 3) (r : Fin 1) (a b : Fin 4) (c : Fin 3) : Bool :=
  (((relationTable.getD h.val []).getD r.val []).getD (4 * c.val + a.val) 0).testBit b.val

lemma checked_start : ∀ c : Fin 3,
    rel (layer 2 0) (evalNat (data.dfa (by decide) (by decide)) 1).1
      (evalNat (data.dfa (by decide) (by decide)) 1).2
      (evalNat (data.dfa (by decide) (by decide)) (3 + c.val)).2 c = true := by
  decide +kernel
lemma checked_step : ∀ (h : Fin 3) (r : Fin 1) (a b : Fin 4)
    (c cp : Fin 3) (d e : Fin 2),
    3*d.val+cp.val=2*c.val+e.val → rel h r a b c = true →
    rel (nextLayer h) (nextParent (by decide) r d.val) (data.step r a d)
      (data.step (outputParent (by decide) r c.val) b e) cp = true := by
  decide +kernel
lemma checked_finish : ∀ (r : Fin 1) (a b : Fin 4) (c : Fin 2),
    rel (layer 2 2) r a b ⟨c.val, by omega⟩ = true → data.test r a = true →
    data.test (outputParent (by decide) r c.val) b = true := by
  decide +kernel
lemma checked_boundary : ∀ n : Fin (3 * 2 ^ 2 + 2), 2 ^ 2 ≤ n.val →
    Nat.digits 3 n.val ⊆ [0,1] →
    data.test (evalNat (data.dfa (by decide) (by decide)) n.val).1
      (evalNat (data.dfa (by decide) (by decide)) n.val).2 = true := by
  decide +kernel
lemma checked_tail_step : ∀ (r : Fin 1) (a : Fin 4), data.tail r a = true →
    data.tail (nextParent (by decide) r 0) (data.step r a 0) = true := by
  decide +kernel
lemma checked_tail_reject : ∀ (r : Fin 1) (a : Fin 4), data.tail r a = true →
    data.test r a = false := by
  decide +kernel

/-- Control only: the necessary power-tail seed is FALSE. -/
lemma no_seed : ¬ (data.tail (evalNat (data.dfa (by decide) (by decide)) (2 ^ 40)).1 (evalNat (data.dfa (by decide) (by decide)) (2 ^ 40)).2 = true) := by decide +kernel
#print axioms checked_start
#print axioms checked_step
#print axioms checked_finish
#print axioms checked_boundary
#print axioms checked_tail_step
#print axioms checked_tail_reject
lemma strict_closure_fails :
    data.test (evalNat (data.dfa (by decide) (by decide)) 1).1
      (evalNat (data.dfa (by decide) (by decide)) 1).2 = true ∧
    data.test (evalNat (data.dfa (by decide) (by decide)) 3).1
      (evalNat (data.dfa (by decide) (by decide)) 3).2 = false := by
  decide +kernel
#print axioms strict_closure_fails
#print axioms no_seed
end Erdos406BinaryEventualExport
