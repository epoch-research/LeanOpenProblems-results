import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_156 : Matches 156 := by decide +kernel
lemma match_part156 : FiniteIntervals.Covers MatchesAt 156 157 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 156 1
  intro i
  fin_cases i
  intro h
  exact matches_156
lemma matches_157 : Matches 157 := by decide +kernel
lemma match_part157 : FiniteIntervals.Covers MatchesAt 157 158 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 157 1
  intro i
  fin_cases i
  intro h
  exact matches_157
lemma matches_158 : Matches 158 := by decide +kernel
lemma match_part158 : FiniteIntervals.Covers MatchesAt 158 159 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 158 1
  intro i
  fin_cases i
  intro h
  exact matches_158
lemma matches_159 : Matches 159 := by decide +kernel
lemma match_part159 : FiniteIntervals.Covers MatchesAt 159 160 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 159 1
  intro i
  fin_cases i
  intro h
  exact matches_159
lemma matches_160 : Matches 160 := by decide +kernel
lemma match_part160 : FiniteIntervals.Covers MatchesAt 160 161 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 160 1
  intro i
  fin_cases i
  intro h
  exact matches_160
lemma matches_161 : Matches 161 := by decide +kernel
lemma match_part161 : FiniteIntervals.Covers MatchesAt 161 162 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 161 1
  intro i
  fin_cases i
  intro h
  exact matches_161
lemma matches_162 : Matches 162 := by decide +kernel
lemma match_part162 : FiniteIntervals.Covers MatchesAt 162 163 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 162 1
  intro i
  fin_cases i
  intro h
  exact matches_162
lemma matches_163 : Matches 163 := by decide +kernel
lemma match_part163 : FiniteIntervals.Covers MatchesAt 163 164 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 163 1
  intro i
  fin_cases i
  intro h
  exact matches_163
lemma matches_164 : Matches 164 := by decide +kernel
lemma match_part164 : FiniteIntervals.Covers MatchesAt 164 165 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 164 1
  intro i
  fin_cases i
  intro h
  exact matches_164
lemma matches_165 : Matches 165 := by decide +kernel
lemma match_part165 : FiniteIntervals.Covers MatchesAt 165 166 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 165 1
  intro i
  fin_cases i
  intro h
  exact matches_165
lemma matches_166 : Matches 166 := by decide +kernel
lemma match_part166 : FiniteIntervals.Covers MatchesAt 166 167 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 166 1
  intro i
  fin_cases i
  intro h
  exact matches_166
lemma matches_167 : Matches 167 := by decide +kernel
lemma match_part167 : FiniteIntervals.Covers MatchesAt 167 168 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 167 1
  intro i
  fin_cases i
  intro h
  exact matches_167
lemma matches_interval13 : FiniteIntervals.Covers MatchesAt 156 168 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part156 (FiniteIntervals.merge match_part157 match_part158)) (FiniteIntervals.merge match_part159 (FiniteIntervals.merge match_part160 match_part161))) (FiniteIntervals.merge (FiniteIntervals.merge match_part162 (FiniteIntervals.merge match_part163 match_part164)) (FiniteIntervals.merge match_part165 (FiniteIntervals.merge match_part166 match_part167))))
#print axioms matches_interval13
end Erdos184Work.PureSevenActions
