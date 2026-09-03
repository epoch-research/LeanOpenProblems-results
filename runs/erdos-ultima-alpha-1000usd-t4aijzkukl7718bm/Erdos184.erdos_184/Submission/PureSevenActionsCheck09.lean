import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_108 : Matches 108 := by decide +kernel
lemma match_part108 : FiniteIntervals.Covers MatchesAt 108 109 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 108 1
  intro i
  fin_cases i
  intro h
  exact matches_108
lemma matches_109 : Matches 109 := by decide +kernel
lemma match_part109 : FiniteIntervals.Covers MatchesAt 109 110 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 109 1
  intro i
  fin_cases i
  intro h
  exact matches_109
lemma matches_110 : Matches 110 := by decide +kernel
lemma match_part110 : FiniteIntervals.Covers MatchesAt 110 111 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 110 1
  intro i
  fin_cases i
  intro h
  exact matches_110
lemma matches_111 : Matches 111 := by decide +kernel
lemma match_part111 : FiniteIntervals.Covers MatchesAt 111 112 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 111 1
  intro i
  fin_cases i
  intro h
  exact matches_111
lemma matches_112 : Matches 112 := by decide +kernel
lemma match_part112 : FiniteIntervals.Covers MatchesAt 112 113 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 112 1
  intro i
  fin_cases i
  intro h
  exact matches_112
lemma matches_113 : Matches 113 := by decide +kernel
lemma match_part113 : FiniteIntervals.Covers MatchesAt 113 114 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 113 1
  intro i
  fin_cases i
  intro h
  exact matches_113
lemma matches_114 : Matches 114 := by decide +kernel
lemma match_part114 : FiniteIntervals.Covers MatchesAt 114 115 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 114 1
  intro i
  fin_cases i
  intro h
  exact matches_114
lemma matches_115 : Matches 115 := by decide +kernel
lemma match_part115 : FiniteIntervals.Covers MatchesAt 115 116 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 115 1
  intro i
  fin_cases i
  intro h
  exact matches_115
lemma matches_116 : Matches 116 := by decide +kernel
lemma match_part116 : FiniteIntervals.Covers MatchesAt 116 117 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 116 1
  intro i
  fin_cases i
  intro h
  exact matches_116
lemma matches_117 : Matches 117 := by decide +kernel
lemma match_part117 : FiniteIntervals.Covers MatchesAt 117 118 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 117 1
  intro i
  fin_cases i
  intro h
  exact matches_117
lemma matches_118 : Matches 118 := by decide +kernel
lemma match_part118 : FiniteIntervals.Covers MatchesAt 118 119 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 118 1
  intro i
  fin_cases i
  intro h
  exact matches_118
lemma matches_119 : Matches 119 := by decide +kernel
lemma match_part119 : FiniteIntervals.Covers MatchesAt 119 120 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 119 1
  intro i
  fin_cases i
  intro h
  exact matches_119
lemma matches_interval9 : FiniteIntervals.Covers MatchesAt 108 120 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part108 (FiniteIntervals.merge match_part109 match_part110)) (FiniteIntervals.merge match_part111 (FiniteIntervals.merge match_part112 match_part113))) (FiniteIntervals.merge (FiniteIntervals.merge match_part114 (FiniteIntervals.merge match_part115 match_part116)) (FiniteIntervals.merge match_part117 (FiniteIntervals.merge match_part118 match_part119))))
#print axioms matches_interval9
end Erdos184Work.PureSevenActions
