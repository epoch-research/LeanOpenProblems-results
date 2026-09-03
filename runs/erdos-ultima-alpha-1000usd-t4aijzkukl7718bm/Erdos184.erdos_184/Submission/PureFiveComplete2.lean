import Submission.PureFiveComplete2_000
import Submission.PureFiveComplete2_001
import Submission.PureFiveComplete2_002
import Submission.PureFiveComplete2_003
import Submission.PureFiveComplete2_004
import Submission.PureFiveComplete2_005
import Submission.PureFiveComplete2_006
import Submission.PureFiveComplete2_007

/-! Complete numerical coverage of the projected five-color survivor catalogue. -/
namespace Erdos184Work.PureFiveFilter2
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma interval_complete : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 0 77760 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk0 interval_chunk1) (FiniteIntervals.merge interval_chunk2 interval_chunk3)) (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk4 interval_chunk5) (FiniteIntervals.merge interval_chunk6 (FiniteIntervals.merge interval_chunk7 interval_chunk8)))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk9 interval_chunk10) (FiniteIntervals.merge interval_chunk11 (FiniteIntervals.merge interval_chunk12 interval_chunk13))) (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk14 interval_chunk15) (FiniteIntervals.merge interval_chunk16 (FiniteIntervals.merge interval_chunk17 interval_chunk18))))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk19 interval_chunk20) (FiniteIntervals.merge interval_chunk21 (FiniteIntervals.merge interval_chunk22 interval_chunk23))) (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk24 interval_chunk25) (FiniteIntervals.merge interval_chunk26 (FiniteIntervals.merge interval_chunk27 interval_chunk28)))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk29 interval_chunk30) (FiniteIntervals.merge interval_chunk31 (FiniteIntervals.merge interval_chunk32 interval_chunk33))) (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk34 interval_chunk35) (FiniteIntervals.merge interval_chunk36 (FiniteIntervals.merge interval_chunk37 interval_chunk38)))))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk39 interval_chunk40) (FiniteIntervals.merge interval_chunk41 interval_chunk42)) (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk43 interval_chunk44) (FiniteIntervals.merge interval_chunk45 (FiniteIntervals.merge interval_chunk46 interval_chunk47)))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk48 interval_chunk49) (FiniteIntervals.merge interval_chunk50 (FiniteIntervals.merge interval_chunk51 interval_chunk52))) (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk53 interval_chunk54) (FiniteIntervals.merge interval_chunk55 (FiniteIntervals.merge interval_chunk56 interval_chunk57))))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk58 interval_chunk59) (FiniteIntervals.merge interval_chunk60 (FiniteIntervals.merge interval_chunk61 interval_chunk62))) (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk63 interval_chunk64) (FiniteIntervals.merge interval_chunk65 (FiniteIntervals.merge interval_chunk66 interval_chunk67)))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk68 interval_chunk69) (FiniteIntervals.merge interval_chunk70 (FiniteIntervals.merge interval_chunk71 interval_chunk72))) (FiniteIntervals.merge (FiniteIntervals.merge interval_chunk73 interval_chunk74) (FiniteIntervals.merge interval_chunk75 (FiniteIntervals.merge interval_chunk76 interval_chunk77)))))))
lemma complete {j : ℕ} (hj : j < 77760) (h : Compatible j) :
    (table.lookup j).isSome = true := interval_complete j (Nat.zero_le _) hj h
lemma exists_case_of_compatible {j : ℕ} (hj : j < 77760) (h : Compatible j) :
    ∃ i : Cases, table.lookup j = some i ∧ caseKey i = j :=
  exists_case (complete hj h)
#print axioms complete
#print axioms exists_case_of_compatible
end Erdos184Work.PureFiveFilter2
