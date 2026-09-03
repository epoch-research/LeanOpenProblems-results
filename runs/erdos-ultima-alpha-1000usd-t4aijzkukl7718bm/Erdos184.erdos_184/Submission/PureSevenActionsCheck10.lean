import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_120 : Matches 120 := by decide +kernel
lemma match_part120 : FiniteIntervals.Covers MatchesAt 120 121 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 120 1
  intro i
  fin_cases i
  intro h
  exact matches_120
lemma matches_121 : Matches 121 := by decide +kernel
lemma match_part121 : FiniteIntervals.Covers MatchesAt 121 122 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 121 1
  intro i
  fin_cases i
  intro h
  exact matches_121
lemma matches_122 : Matches 122 := by decide +kernel
lemma match_part122 : FiniteIntervals.Covers MatchesAt 122 123 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 122 1
  intro i
  fin_cases i
  intro h
  exact matches_122
lemma matches_123 : Matches 123 := by decide +kernel
lemma match_part123 : FiniteIntervals.Covers MatchesAt 123 124 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 123 1
  intro i
  fin_cases i
  intro h
  exact matches_123
lemma matches_124 : Matches 124 := by decide +kernel
lemma match_part124 : FiniteIntervals.Covers MatchesAt 124 125 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 124 1
  intro i
  fin_cases i
  intro h
  exact matches_124
lemma matches_125 : Matches 125 := by decide +kernel
lemma match_part125 : FiniteIntervals.Covers MatchesAt 125 126 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 125 1
  intro i
  fin_cases i
  intro h
  exact matches_125
lemma matches_126 : Matches 126 := by decide +kernel
lemma match_part126 : FiniteIntervals.Covers MatchesAt 126 127 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 126 1
  intro i
  fin_cases i
  intro h
  exact matches_126
lemma matches_127 : Matches 127 := by decide +kernel
lemma match_part127 : FiniteIntervals.Covers MatchesAt 127 128 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 127 1
  intro i
  fin_cases i
  intro h
  exact matches_127
lemma matches_128 : Matches 128 := by decide +kernel
lemma match_part128 : FiniteIntervals.Covers MatchesAt 128 129 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 128 1
  intro i
  fin_cases i
  intro h
  exact matches_128
lemma matches_129 : Matches 129 := by decide +kernel
lemma match_part129 : FiniteIntervals.Covers MatchesAt 129 130 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 129 1
  intro i
  fin_cases i
  intro h
  exact matches_129
lemma matches_130 : Matches 130 := by decide +kernel
lemma match_part130 : FiniteIntervals.Covers MatchesAt 130 131 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 130 1
  intro i
  fin_cases i
  intro h
  exact matches_130
lemma matches_131 : Matches 131 := by decide +kernel
lemma match_part131 : FiniteIntervals.Covers MatchesAt 131 132 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 131 1
  intro i
  fin_cases i
  intro h
  exact matches_131
lemma matches_interval10 : FiniteIntervals.Covers MatchesAt 120 132 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part120 (FiniteIntervals.merge match_part121 match_part122)) (FiniteIntervals.merge match_part123 (FiniteIntervals.merge match_part124 match_part125))) (FiniteIntervals.merge (FiniteIntervals.merge match_part126 (FiniteIntervals.merge match_part127 match_part128)) (FiniteIntervals.merge match_part129 (FiniteIntervals.merge match_part130 match_part131))))
#print axioms matches_interval10
end Erdos184Work.PureSevenActions
