import Submission.PureSixComplete4_000
import Submission.PureSixComplete4_001
import Submission.PureSixComplete4_002
import Submission.PureSixComplete4_003
import Submission.PureSixComplete4_004
import Submission.PureSixComplete4_005
import Submission.PureSixComplete4_006
import Submission.PureSixComplete4_007
import Submission.PureSixComplete4_008
import Submission.PureSixComplete4_009
import Submission.PureSixComplete4_010
import Submission.PureSixComplete4_011
import Submission.PureSixComplete4_012
import Submission.PureSixComplete4_013
import Submission.PureSixComplete4_014
import Submission.PureSixComplete4_015
import Submission.PureSixComplete4_016
import Submission.PureSixComplete4_017
import Submission.PureSixComplete4_018
import Submission.PureSixComplete4_019
import Submission.PureSixComplete4_020
import Submission.PureSixComplete4_021
import Submission.PureSixComplete4_022
import Submission.PureSixComplete4_023
import Submission.PureSixComplete4_024
import Submission.PureSixComplete4_025
import Submission.PureSixComplete4_026
import Submission.PureSixComplete4_027
import Submission.PureSixComplete4_028
import Submission.PureSixComplete4_029
import Submission.PureSixComplete4_030
import Submission.PureSixComplete4_031
import Submission.PureSixComplete4_032
import Submission.PureSixComplete4_033
import Submission.PureSixComplete4_034
import Submission.PureSixComplete4_035
import Submission.PureSixComplete4_036
import Submission.PureSixComplete4_037
import Submission.PureSixComplete4_038
import Submission.PureSixComplete4_039
import Submission.PureSixComplete4_040
import Submission.PureSixComplete4_041
import Submission.PureSixComplete4_042
import Submission.PureSixComplete4_043
import Submission.PureSixComplete4_044
import Submission.PureSixComplete4_045
import Submission.PureSixComplete4_046
import Submission.PureSixComplete4_047
import Submission.PureSixComplete4_048
import Submission.PureSixComplete4_049
import Submission.PureSixComplete4_050
import Submission.PureSixComplete4_051
import Submission.PureSixComplete4_052
import Submission.PureSixComplete4_053
import Submission.PureSixComplete4_054
import Submission.PureSixComplete4_055
import Submission.PureSixComplete4_056
import Submission.PureSixComplete4_057
import Submission.PureSixComplete4_058
import Submission.PureSixComplete4_059
import Submission.PureSixComplete4_060
import Submission.PureSixComplete4_061
import Submission.PureSixComplete4_062
import Submission.PureSixComplete4_063
import Submission.PureSixComplete4_064
import Submission.PureSixComplete4_065
import Submission.PureSixComplete4_066
import Submission.PureSixComplete4_067
import Submission.PureSixComplete4_068
import Submission.PureSixComplete4_069
import Submission.PureSixComplete4_070
import Submission.PureSixComplete4_071
import Submission.PureSixComplete4_072
import Submission.PureSixComplete4_073
import Submission.PureSixComplete4_074
import Submission.PureSixComplete4_075
import Submission.PureSixComplete4_076
import Submission.PureSixComplete4_077
import Submission.PureSixComplete4_078
import Submission.PureSixComplete4_079

namespace Erdos184Work.PureSixLocalFilter4
open PureSixRowModel4
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
  · exact complete_case24
  · exact complete_case25
  · exact complete_case26
  · exact complete_case27
  · exact complete_case28
  · exact complete_case29
  · exact complete_case30
  · exact complete_case31
  · exact complete_case32
  · exact complete_case33
  · exact complete_case34
  · exact complete_case35
  · exact complete_case36
  · exact complete_case37
  · exact complete_case38
  · exact complete_case39
  · exact complete_case40
  · exact complete_case41
  · exact complete_case42
  · exact complete_case43
  · exact complete_case44
  · exact complete_case45
  · exact complete_case46
  · exact complete_case47
  · exact complete_case48
  · exact complete_case49
  · exact complete_case50
  · exact complete_case51
  · exact complete_case52
  · exact complete_case53
  · exact complete_case54
  · exact complete_case55
  · exact complete_case56
  · exact complete_case57
  · exact complete_case58
  · exact complete_case59
  · exact complete_case60
  · exact complete_case61
  · exact complete_case62
  · exact complete_case63
  · exact complete_case64
  · exact complete_case65
  · exact complete_case66
  · exact complete_case67
  · exact complete_case68
  · exact complete_case69
  · exact complete_case70
  · exact complete_case71
  · exact complete_case72
  · exact complete_case73
  · exact complete_case74
  · exact complete_case75
  · exact complete_case76
  · exact complete_case77
  · exact complete_case78
  · exact complete_case79
lemma complete_rows (q0 : Fin 360) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) (h : Compatible q0 q1 q2 q3 q4 q5) :
    (output.lookup (key (rows q0 q1 q2 q3 q4 q5))).isSome = true :=
  complete_of_factored complete_factored q0 q1 q2 q3 q4 q5 h
lemma complete {j : ℕ} (hj : j < 2239488000) (h : Compatible (digit0 j) (digit1 j) (digit2 j) (digit3 j) (digit4 j) (digit5 j)) :
    (output.lookup j).isSome = true := by
  have hh := complete_rows (digit0 j) (digit1 j) (digit2 j) (digit3 j) (digit4 j) (digit5 j) h
  change (output.lookup (key (unkey j))).isSome = true at hh
  rwa [key_unkey hj] at hh
#print axioms complete
end Erdos184Work.PureSixLocalFilter4
