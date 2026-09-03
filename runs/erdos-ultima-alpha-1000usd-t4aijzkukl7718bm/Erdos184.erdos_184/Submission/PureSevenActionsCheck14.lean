import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_168 : Matches 168 := by decide +kernel
lemma match_part168 : FiniteIntervals.Covers MatchesAt 168 169 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 168 1
  intro i
  fin_cases i
  intro h
  exact matches_168
lemma matches_169 : Matches 169 := by decide +kernel
lemma match_part169 : FiniteIntervals.Covers MatchesAt 169 170 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 169 1
  intro i
  fin_cases i
  intro h
  exact matches_169
lemma matches_170 : Matches 170 := by decide +kernel
lemma match_part170 : FiniteIntervals.Covers MatchesAt 170 171 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 170 1
  intro i
  fin_cases i
  intro h
  exact matches_170
lemma matches_171 : Matches 171 := by decide +kernel
lemma match_part171 : FiniteIntervals.Covers MatchesAt 171 172 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 171 1
  intro i
  fin_cases i
  intro h
  exact matches_171
lemma matches_172 : Matches 172 := by decide +kernel
lemma match_part172 : FiniteIntervals.Covers MatchesAt 172 173 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 172 1
  intro i
  fin_cases i
  intro h
  exact matches_172
lemma matches_173 : Matches 173 := by decide +kernel
lemma match_part173 : FiniteIntervals.Covers MatchesAt 173 174 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 173 1
  intro i
  fin_cases i
  intro h
  exact matches_173
lemma matches_174 : Matches 174 := by decide +kernel
lemma match_part174 : FiniteIntervals.Covers MatchesAt 174 175 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 174 1
  intro i
  fin_cases i
  intro h
  exact matches_174
lemma matches_175 : Matches 175 := by decide +kernel
lemma match_part175 : FiniteIntervals.Covers MatchesAt 175 176 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 175 1
  intro i
  fin_cases i
  intro h
  exact matches_175
lemma matches_176 : Matches 176 := by decide +kernel
lemma match_part176 : FiniteIntervals.Covers MatchesAt 176 177 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 176 1
  intro i
  fin_cases i
  intro h
  exact matches_176
lemma matches_177 : Matches 177 := by decide +kernel
lemma match_part177 : FiniteIntervals.Covers MatchesAt 177 178 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 177 1
  intro i
  fin_cases i
  intro h
  exact matches_177
lemma matches_178 : Matches 178 := by decide +kernel
lemma match_part178 : FiniteIntervals.Covers MatchesAt 178 179 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 178 1
  intro i
  fin_cases i
  intro h
  exact matches_178
lemma matches_179 : Matches 179 := by decide +kernel
lemma match_part179 : FiniteIntervals.Covers MatchesAt 179 180 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 179 1
  intro i
  fin_cases i
  intro h
  exact matches_179
lemma matches_interval14 : FiniteIntervals.Covers MatchesAt 168 180 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part168 (FiniteIntervals.merge match_part169 match_part170)) (FiniteIntervals.merge match_part171 (FiniteIntervals.merge match_part172 match_part173))) (FiniteIntervals.merge (FiniteIntervals.merge match_part174 (FiniteIntervals.merge match_part175 match_part176)) (FiniteIntervals.merge match_part177 (FiniteIntervals.merge match_part178 match_part179))))
#print axioms matches_interval14
end Erdos184Work.PureSevenActions
