import Submission.PureFiveComplete4_000
import Submission.PureFiveComplete4_001
import Submission.PureFiveComplete4_002
import Submission.PureFiveComplete4_003
import Submission.PureFiveComplete4_004
import Submission.PureFiveComplete4_005
import Submission.PureFiveComplete4_006
import Submission.PureFiveComplete4_007
import Submission.PureFiveComplete4_008
import Submission.PureFiveComplete4_009
import Submission.PureFiveComplete4_010
import Submission.PureFiveComplete4_011
import Submission.PureFiveComplete4_012
import Submission.PureFiveComplete4_013
import Submission.PureFiveComplete4_014
import Submission.PureFiveComplete4_015
import Submission.PureFiveComplete4_016
import Submission.PureFiveComplete4_017
import Submission.PureFiveComplete4_018
import Submission.PureFiveComplete4_019
import Submission.PureFiveComplete4_020
import Submission.PureFiveComplete4_021
import Submission.PureFiveComplete4_022
import Submission.PureFiveComplete4_023
import Submission.PureFiveComplete4_024
import Submission.PureFiveComplete4_025
import Submission.PureFiveComplete4_026
import Submission.PureFiveComplete4_027
import Submission.PureFiveComplete4_028
import Submission.PureFiveComplete4_029
import Submission.PureFiveComplete4_030
import Submission.PureFiveComplete4_031
import Submission.PureFiveComplete4_032
import Submission.PureFiveComplete4_033
import Submission.PureFiveComplete4_034
import Submission.PureFiveComplete4_035
import Submission.PureFiveComplete4_036
import Submission.PureFiveComplete4_037
import Submission.PureFiveComplete4_038
import Submission.PureFiveComplete4_039
import Submission.PureFiveComplete4_040
import Submission.PureFiveComplete4_041
import Submission.PureFiveComplete4_042
import Submission.PureFiveComplete4_043
import Submission.PureFiveComplete4_044
import Submission.PureFiveComplete4_045
import Submission.PureFiveComplete4_046
import Submission.PureFiveComplete4_047
import Submission.PureFiveComplete4_048
import Submission.PureFiveComplete4_049
import Submission.PureFiveComplete4_050
import Submission.PureFiveComplete4_051
import Submission.PureFiveComplete4_052
import Submission.PureFiveComplete4_053
import Submission.PureFiveComplete4_054
import Submission.PureFiveComplete4_055
import Submission.PureFiveComplete4_056
import Submission.PureFiveComplete4_057
import Submission.PureFiveComplete4_058
import Submission.PureFiveComplete4_059
import Mathlib.Tactic.FinCases

/-! Complete coverage assembled from factored row-key checks. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma ordered_complete (q0 : Fin 60) : OrderedComplete q0 := by
  fin_cases q0
  · exact ordered_0
  · exact ordered_1
  · exact ordered_2
  · exact ordered_3
  · exact ordered_4
  · exact ordered_5
  · exact ordered_6
  · exact ordered_7
  · exact ordered_8
  · exact ordered_9
  · exact ordered_10
  · exact ordered_11
  · exact ordered_12
  · exact ordered_13
  · exact ordered_14
  · exact ordered_15
  · exact ordered_16
  · exact ordered_17
  · exact ordered_18
  · exact ordered_19
  · exact ordered_20
  · exact ordered_21
  · exact ordered_22
  · exact ordered_23
  · exact ordered_24
  · exact ordered_25
  · exact ordered_26
  · exact ordered_27
  · exact ordered_28
  · exact ordered_29
  · exact ordered_30
  · exact ordered_31
  · exact ordered_32
  · exact ordered_33
  · exact ordered_34
  · exact ordered_35
  · exact ordered_36
  · exact ordered_37
  · exact ordered_38
  · exact ordered_39
  · exact ordered_40
  · exact ordered_41
  · exact ordered_42
  · exact ordered_43
  · exact ordered_44
  · exact ordered_45
  · exact ordered_46
  · exact ordered_47
  · exact ordered_48
  · exact ordered_49
  · exact ordered_50
  · exact ordered_51
  · exact ordered_52
  · exact ordered_53
  · exact ordered_54
  · exact ordered_55
  · exact ordered_56
  · exact ordered_57
  · exact ordered_58
  · exact ordered_59

lemma complete {j : ℕ} (hj : j < 1244160) (h : Compatible j) :
    (table.lookup j).isSome = true := by
  rcases h with ⟨h0,h1,h2,h3,h4⟩
  change RowC0 0 (digit1 j) (digit2 j) (digit3 j) (digit4 j) at h0
  change RowC1 (digit0 j) 0 (digit2 j) (digit3 j) (digit4 j) at h1
  change RowC2 (digit0 j) (digit1 j) 0 (digit3 j) (digit4 j) at h2
  change RowC3 (digit0 j) (digit1 j) (digit2 j) 0 (digit4 j) at h3
  change RowC4 (digit0 j) (digit1 j) (digit2 j) (digit3 j) 0 at h4
  have hh := ordered_complete (digit0 j) (digit3 j) (digit4 j) (digit1 j) h2
    (digit2 j) h1 h0 h3 h4
  rwa [rowKey_digits hj] at hh
lemma interval_complete : FiniteIntervals.Covers
    (fun j => Compatible j → (table.lookup j).isSome = true) 0 1244160 := by
  intro j _ hj h
  exact complete hj h
lemma exists_case_of_compatible {j : ℕ} (hj : j < 1244160) (h : Compatible j) :
    ∃ i : Cases, table.lookup j = some i ∧ caseKey i = j :=
  exists_case (complete hj h)
#print axioms complete
#print axioms exists_case_of_compatible
end Erdos184Work.PureFiveFilter4
