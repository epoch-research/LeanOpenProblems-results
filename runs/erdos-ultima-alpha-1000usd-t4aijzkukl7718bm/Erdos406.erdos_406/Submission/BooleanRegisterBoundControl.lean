import Submission.BooleanRegisterFailureBound

/-! Finite-data check. Control mode does not assert finiteness. -/

namespace Erdos406BoundedRegisterExport
open Erdos406BooleanRegister
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 20000

def stepRows : List (List ℕ) := [[8, 1, 8], [8, 8, 2], [8, 8, 3], [8, 4, 8], [5, 8, 8], [8, 6, 8], [8, 7, 8], [8, 8, 8], [8, 8, 8]]
def acceptRows : List Bool := [true, true, true, true, true, true, true, false, true]
def goodRows : List Bool := [true, true, false, false, false, false, false, false, true]
def relationRows : List (List ℕ) := [[1, 0, 0, 0], [0, 2, 0, 0], [0, 0, 0, 256], [0, 0, 0, 256], [0, 0, 256, 0], [256, 0, 0, 0], [0, 256, 0, 0], [0, 256, 0, 0], [432, 332, 256, 256]]
def potentialRows : List (List (List ℕ)) := [[[1024, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 341, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 113]], [[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 37]], [[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]]]

def F : FiniteData 9 where
  step p d := ⟨((stepRows.getD p.val []).getD d.val 0) % 9, Nat.mod_lt _ (by decide)⟩
  start := 0
  test p := acceptRows.getD p.val false
  good p := goodRows.getD p.val false
  relation p q c := ((relationRows.getD p.val []).getD c.val 0).testBit q.val

def V (p q : Fin 9) (c : Fin 4) : ℕ :=
  (((potentialRows.getD p.val []).getD c.val []).getD q.val 0)

lemma checked_start : F.relation F.start F.start 0 = true := by decide +kernel
lemma checked_good_start : F.good F.start = true := by decide +kernel
lemma checked_good_step : ∀ (s : Fin 9) (d : Fin 2), F.good s = true →
    F.good (F.step s (digit d.val)) = true := by decide +kernel
lemma checked_good_end : ∀ (s : Fin 9), F.good s = true →
    F.test (F.step s (digit 1)) = true := by decide +kernel
lemma step_0 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (0 : Fin 9) t c = true →
    F.relation (F.step (0 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) = true := by decide +kernel
lemma step_1 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (1 : Fin 9) t c = true →
    F.relation (F.step (1 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) = true := by decide +kernel
lemma step_2 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (2 : Fin 9) t c = true →
    F.relation (F.step (2 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) = true := by decide +kernel
lemma step_3 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (3 : Fin 9) t c = true →
    F.relation (F.step (3 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) = true := by decide +kernel
lemma step_4 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (4 : Fin 9) t c = true →
    F.relation (F.step (4 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) = true := by decide +kernel
lemma step_5 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (5 : Fin 9) t c = true →
    F.relation (F.step (5 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) = true := by decide +kernel
lemma step_6 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (6 : Fin 9) t c = true →
    F.relation (F.step (6 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) = true := by decide +kernel
lemma step_7 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (7 : Fin 9) t c = true →
    F.relation (F.step (7 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) = true := by decide +kernel
lemma step_8 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (8 : Fin 9) t c = true →
    F.relation (F.step (8 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) = true := by decide +kernel
lemma checked_step : ∀ (s : Fin 9), ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation s t c = true →
    F.relation (F.step s d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) = true := by
  intro s
  fin_cases s
  · exact step_0
  · exact step_1
  · exact step_2
  · exact step_3
  · exact step_4
  · exact step_5
  · exact step_6
  · exact step_7
  · exact step_8
#print axioms checked_step
lemma bound_0 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (0 : Fin 9) t c = true →
    0 < V (F.step (0 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) →
    d.val + 3 * V (F.step (0 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) ≤ V (0 : Fin 9) t c := by decide +kernel
lemma bound_1 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (1 : Fin 9) t c = true →
    0 < V (F.step (1 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) →
    d.val + 3 * V (F.step (1 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) ≤ V (1 : Fin 9) t c := by decide +kernel
lemma bound_2 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (2 : Fin 9) t c = true →
    0 < V (F.step (2 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) →
    d.val + 3 * V (F.step (2 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) ≤ V (2 : Fin 9) t c := by decide +kernel
lemma bound_3 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (3 : Fin 9) t c = true →
    0 < V (F.step (3 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) →
    d.val + 3 * V (F.step (3 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) ≤ V (3 : Fin 9) t c := by decide +kernel
lemma bound_4 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (4 : Fin 9) t c = true →
    0 < V (F.step (4 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) →
    d.val + 3 * V (F.step (4 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) ≤ V (4 : Fin 9) t c := by decide +kernel
lemma bound_5 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (5 : Fin 9) t c = true →
    0 < V (F.step (5 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) →
    d.val + 3 * V (F.step (5 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) ≤ V (5 : Fin 9) t c := by decide +kernel
lemma bound_6 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (6 : Fin 9) t c = true →
    0 < V (F.step (6 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) →
    d.val + 3 * V (F.step (6 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) ≤ V (6 : Fin 9) t c := by decide +kernel
lemma bound_7 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (7 : Fin 9) t c = true →
    0 < V (F.step (7 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) →
    d.val + 3 * V (F.step (7 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) ≤ V (7 : Fin 9) t c := by decide +kernel
lemma bound_8 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation (8 : Fin 9) t c = true →
    0 < V (F.step (8 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) →
    d.val + 3 * V (F.step (8 : Fin 9) d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) ≤ V (8 : Fin 9) t c := by decide +kernel
lemma checked_bound : ∀ (s : Fin 9), ∀ (t : Fin 9) (c : Fin 4) (d : Fin 3), F.relation s t c = true →
    0 < V (F.step s d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) →
    d.val + 3 * V (F.step s d) (F.step t (digit (4 * d.val + c.val)))
      (carry ((4 * d.val + c.val) / 3)) ≤ V s t c := by
  intro s
  fin_cases s
  · exact bound_0
  · exact bound_1
  · exact bound_2
  · exact bound_3
  · exact bound_4
  · exact bound_5
  · exact bound_6
  · exact bound_7
  · exact bound_8
#print axioms checked_bound
lemma end_0 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 2), F.relation (0 : Fin 9) t c = true →
    F.test (F.step (0 : Fin 9) (digit (d.val + 1))) = false →
    F.test (F.toData.dfa.evalFrom (F.step t (digit (4 * (d.val + 1) + c.val)))
      (Nat.digits 3 ((4 * (d.val + 1) + c.val) / 3))) = true →
    d.val + 1 ≤ V (0 : Fin 9) t c := by decide +kernel
lemma end_1 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 2), F.relation (1 : Fin 9) t c = true →
    F.test (F.step (1 : Fin 9) (digit (d.val + 1))) = false →
    F.test (F.toData.dfa.evalFrom (F.step t (digit (4 * (d.val + 1) + c.val)))
      (Nat.digits 3 ((4 * (d.val + 1) + c.val) / 3))) = true →
    d.val + 1 ≤ V (1 : Fin 9) t c := by decide +kernel
lemma end_2 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 2), F.relation (2 : Fin 9) t c = true →
    F.test (F.step (2 : Fin 9) (digit (d.val + 1))) = false →
    F.test (F.toData.dfa.evalFrom (F.step t (digit (4 * (d.val + 1) + c.val)))
      (Nat.digits 3 ((4 * (d.val + 1) + c.val) / 3))) = true →
    d.val + 1 ≤ V (2 : Fin 9) t c := by decide +kernel
lemma end_3 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 2), F.relation (3 : Fin 9) t c = true →
    F.test (F.step (3 : Fin 9) (digit (d.val + 1))) = false →
    F.test (F.toData.dfa.evalFrom (F.step t (digit (4 * (d.val + 1) + c.val)))
      (Nat.digits 3 ((4 * (d.val + 1) + c.val) / 3))) = true →
    d.val + 1 ≤ V (3 : Fin 9) t c := by decide +kernel
lemma end_4 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 2), F.relation (4 : Fin 9) t c = true →
    F.test (F.step (4 : Fin 9) (digit (d.val + 1))) = false →
    F.test (F.toData.dfa.evalFrom (F.step t (digit (4 * (d.val + 1) + c.val)))
      (Nat.digits 3 ((4 * (d.val + 1) + c.val) / 3))) = true →
    d.val + 1 ≤ V (4 : Fin 9) t c := by decide +kernel
lemma end_5 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 2), F.relation (5 : Fin 9) t c = true →
    F.test (F.step (5 : Fin 9) (digit (d.val + 1))) = false →
    F.test (F.toData.dfa.evalFrom (F.step t (digit (4 * (d.val + 1) + c.val)))
      (Nat.digits 3 ((4 * (d.val + 1) + c.val) / 3))) = true →
    d.val + 1 ≤ V (5 : Fin 9) t c := by decide +kernel
lemma end_6 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 2), F.relation (6 : Fin 9) t c = true →
    F.test (F.step (6 : Fin 9) (digit (d.val + 1))) = false →
    F.test (F.toData.dfa.evalFrom (F.step t (digit (4 * (d.val + 1) + c.val)))
      (Nat.digits 3 ((4 * (d.val + 1) + c.val) / 3))) = true →
    d.val + 1 ≤ V (6 : Fin 9) t c := by decide +kernel
lemma end_7 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 2), F.relation (7 : Fin 9) t c = true →
    F.test (F.step (7 : Fin 9) (digit (d.val + 1))) = false →
    F.test (F.toData.dfa.evalFrom (F.step t (digit (4 * (d.val + 1) + c.val)))
      (Nat.digits 3 ((4 * (d.val + 1) + c.val) / 3))) = true →
    d.val + 1 ≤ V (7 : Fin 9) t c := by decide +kernel
lemma end_8 : ∀ (t : Fin 9) (c : Fin 4) (d : Fin 2), F.relation (8 : Fin 9) t c = true →
    F.test (F.step (8 : Fin 9) (digit (d.val + 1))) = false →
    F.test (F.toData.dfa.evalFrom (F.step t (digit (4 * (d.val + 1) + c.val)))
      (Nat.digits 3 ((4 * (d.val + 1) + c.val) / 3))) = true →
    d.val + 1 ≤ V (8 : Fin 9) t c := by decide +kernel
lemma checked_end : ∀ (s : Fin 9), ∀ (t : Fin 9) (c : Fin 4) (d : Fin 2), F.relation s t c = true →
    F.test (F.step s (digit (d.val + 1))) = false →
    F.test (F.toData.dfa.evalFrom (F.step t (digit (4 * (d.val + 1) + c.val)))
      (Nat.digits 3 ((4 * (d.val + 1) + c.val) / 3))) = true →
    d.val + 1 ≤ V s t c := by
  intro s
  fin_cases s
  · exact end_0
  · exact end_1
  · exact end_2
  · exact end_3
  · exact end_4
  · exact end_5
  · exact end_6
  · exact end_7
  · exact end_8
#print axioms checked_end
lemma root_value : V F.start F.start 0 = 1024 := by decide +kernel
lemma checked_seed : F.test (F.toData.dfa.eval (Nat.digits 3 (4 ^ 5))) = false := by decide +kernel
#print axioms checked_seed
/-- This diagnostic fails the necessary strict-root condition. -/
lemma control_root_not_below : ¬ V F.start F.start 0 < 4 ^ 5 := by decide +kernel
#print axioms control_root_not_below
end Erdos406BoundedRegisterExport
