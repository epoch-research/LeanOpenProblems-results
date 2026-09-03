import Submission.PureFiveComplete1_000

/-! Complete numerical coverage of the projected five-color survivor catalogue. -/
namespace Erdos184Work.PureFiveFilter1
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma interval_complete : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 0 3888 :=
  (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk0 interval_chunk1) (FiniteIntervals.merge interval_chunk2 interval_chunk3))
lemma complete {j : ℕ} (hj : j < 3888) (h : Compatible j) :
    (table.lookup j).isSome = true := interval_complete j (Nat.zero_le _) hj h
lemma exists_case_of_compatible {j : ℕ} (hj : j < 3888) (h : Compatible j) :
    ∃ i : Cases, table.lookup j = some i ∧ caseKey i = j :=
  exists_case (complete hj h)
#print axioms complete
#print axioms exists_case_of_compatible
end Erdos184Work.PureFiveFilter1
