import Submission.PureSixComplete3_000
import Submission.PureSixComplete3_001
import Submission.PureSixComplete3_002
import Submission.PureSixComplete3_003
import Submission.PureSixComplete3_004
import Submission.PureSixComplete3_005
import Submission.PureSixComplete3_006
import Submission.PureSixComplete3_007
import Submission.PureSixComplete3_008
import Submission.PureSixComplete3_009
import Submission.PureSixComplete3_010
import Submission.PureSixComplete3_011
import Submission.PureSixComplete3_012
import Submission.PureSixComplete3_013
import Submission.PureSixComplete3_014
import Submission.PureSixComplete3_015
import Submission.PureSixComplete3_016
import Submission.PureSixComplete3_017
import Submission.PureSixComplete3_018
import Submission.PureSixComplete3_019
import Submission.PureSixComplete3_020
import Submission.PureSixComplete3_021
import Submission.PureSixComplete3_022
import Submission.PureSixComplete3_023

namespace Erdos184Work.PureSixLocalFilter3
open PureSixRowModel3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_factored : ∀ t e0, CompleteAt t e0 := by
  intro t
  fin_cases t
  · exact complete_case0
  · exact complete_case1
  · exact complete_case2
  · exact complete_case3
  · exact complete_case4
  · exact complete_case5
  · exact complete_case6
  · exact complete_case7
  · exact complete_case8
  · exact complete_case9
  · exact complete_case10
  · exact complete_case11
  · exact complete_case12
  · exact complete_case13
  · exact complete_case14
  · exact complete_case15
  · exact complete_case16
  · exact complete_case17
  · exact complete_case18
  · exact complete_case19
  · exact complete_case20
  · exact complete_case21
  · exact complete_case22
  · exact complete_case23
lemma complete_rows (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) (h : Compatible q0 q1 q2 q3 q4 q5) :
    (output.lookup (key (rows q0 q1 q2 q3 q4 q5))).isSome = true :=
  complete_of_factored complete_factored q0 q1 q2 q3 q4 q5 h
lemma complete {j : ℕ} (hj : j < 46656000000) (h : Compatible (digit0 j) (digit1 j) (digit2 j) (digit3 j) (digit4 j) (digit5 j)) :
    (output.lookup j).isSome = true := by
  have hh := complete_rows (digit0 j) (digit1 j) (digit2 j) (digit3 j) (digit4 j) (digit5 j) h
  change (output.lookup (key (unkey j))).isSome = true at hh
  rwa [key_unkey hj] at hh
#print axioms complete
end Erdos184Work.PureSixLocalFilter3
