import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_132 : Matches 132 := by decide +kernel
lemma match_part132 : FiniteIntervals.Covers MatchesAt 132 133 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 132 1
  intro i
  fin_cases i
  intro h
  exact matches_132
lemma matches_133 : Matches 133 := by decide +kernel
lemma match_part133 : FiniteIntervals.Covers MatchesAt 133 134 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 133 1
  intro i
  fin_cases i
  intro h
  exact matches_133
lemma matches_134 : Matches 134 := by decide +kernel
lemma match_part134 : FiniteIntervals.Covers MatchesAt 134 135 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 134 1
  intro i
  fin_cases i
  intro h
  exact matches_134
lemma matches_135 : Matches 135 := by decide +kernel
lemma match_part135 : FiniteIntervals.Covers MatchesAt 135 136 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 135 1
  intro i
  fin_cases i
  intro h
  exact matches_135
lemma matches_136 : Matches 136 := by decide +kernel
lemma match_part136 : FiniteIntervals.Covers MatchesAt 136 137 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 136 1
  intro i
  fin_cases i
  intro h
  exact matches_136
lemma matches_137 : Matches 137 := by decide +kernel
lemma match_part137 : FiniteIntervals.Covers MatchesAt 137 138 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 137 1
  intro i
  fin_cases i
  intro h
  exact matches_137
lemma matches_138 : Matches 138 := by decide +kernel
lemma match_part138 : FiniteIntervals.Covers MatchesAt 138 139 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 138 1
  intro i
  fin_cases i
  intro h
  exact matches_138
lemma matches_139 : Matches 139 := by decide +kernel
lemma match_part139 : FiniteIntervals.Covers MatchesAt 139 140 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 139 1
  intro i
  fin_cases i
  intro h
  exact matches_139
lemma matches_140 : Matches 140 := by decide +kernel
lemma match_part140 : FiniteIntervals.Covers MatchesAt 140 141 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 140 1
  intro i
  fin_cases i
  intro h
  exact matches_140
lemma matches_141 : Matches 141 := by decide +kernel
lemma match_part141 : FiniteIntervals.Covers MatchesAt 141 142 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 141 1
  intro i
  fin_cases i
  intro h
  exact matches_141
lemma matches_142 : Matches 142 := by decide +kernel
lemma match_part142 : FiniteIntervals.Covers MatchesAt 142 143 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 142 1
  intro i
  fin_cases i
  intro h
  exact matches_142
lemma matches_143 : Matches 143 := by decide +kernel
lemma match_part143 : FiniteIntervals.Covers MatchesAt 143 144 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 143 1
  intro i
  fin_cases i
  intro h
  exact matches_143
lemma matches_interval11 : FiniteIntervals.Covers MatchesAt 132 144 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part132 (FiniteIntervals.merge match_part133 match_part134)) (FiniteIntervals.merge match_part135 (FiniteIntervals.merge match_part136 match_part137))) (FiniteIntervals.merge (FiniteIntervals.merge match_part138 (FiniteIntervals.merge match_part139 match_part140)) (FiniteIntervals.merge match_part141 (FiniteIntervals.merge match_part142 match_part143))))
#print axioms matches_interval11
end Erdos184Work.PureSevenActions
