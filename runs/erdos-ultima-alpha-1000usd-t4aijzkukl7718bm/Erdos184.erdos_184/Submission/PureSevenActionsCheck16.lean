import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_192 : Matches 192 := by decide +kernel
lemma match_part192 : FiniteIntervals.Covers MatchesAt 192 193 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 192 1
  intro i
  fin_cases i
  intro h
  exact matches_192
lemma matches_193 : Matches 193 := by decide +kernel
lemma match_part193 : FiniteIntervals.Covers MatchesAt 193 194 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 193 1
  intro i
  fin_cases i
  intro h
  exact matches_193
lemma matches_194 : Matches 194 := by decide +kernel
lemma match_part194 : FiniteIntervals.Covers MatchesAt 194 195 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 194 1
  intro i
  fin_cases i
  intro h
  exact matches_194
lemma matches_195 : Matches 195 := by decide +kernel
lemma match_part195 : FiniteIntervals.Covers MatchesAt 195 196 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 195 1
  intro i
  fin_cases i
  intro h
  exact matches_195
lemma matches_196 : Matches 196 := by decide +kernel
lemma match_part196 : FiniteIntervals.Covers MatchesAt 196 197 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 196 1
  intro i
  fin_cases i
  intro h
  exact matches_196
lemma matches_197 : Matches 197 := by decide +kernel
lemma match_part197 : FiniteIntervals.Covers MatchesAt 197 198 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 197 1
  intro i
  fin_cases i
  intro h
  exact matches_197
lemma matches_198 : Matches 198 := by decide +kernel
lemma match_part198 : FiniteIntervals.Covers MatchesAt 198 199 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 198 1
  intro i
  fin_cases i
  intro h
  exact matches_198
lemma matches_199 : Matches 199 := by decide +kernel
lemma match_part199 : FiniteIntervals.Covers MatchesAt 199 200 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 199 1
  intro i
  fin_cases i
  intro h
  exact matches_199
lemma matches_200 : Matches 200 := by decide +kernel
lemma match_part200 : FiniteIntervals.Covers MatchesAt 200 201 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 200 1
  intro i
  fin_cases i
  intro h
  exact matches_200
lemma matches_201 : Matches 201 := by decide +kernel
lemma match_part201 : FiniteIntervals.Covers MatchesAt 201 202 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 201 1
  intro i
  fin_cases i
  intro h
  exact matches_201
lemma matches_202 : Matches 202 := by decide +kernel
lemma match_part202 : FiniteIntervals.Covers MatchesAt 202 203 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 202 1
  intro i
  fin_cases i
  intro h
  exact matches_202
lemma matches_203 : Matches 203 := by decide +kernel
lemma match_part203 : FiniteIntervals.Covers MatchesAt 203 204 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 203 1
  intro i
  fin_cases i
  intro h
  exact matches_203
lemma matches_interval16 : FiniteIntervals.Covers MatchesAt 192 204 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part192 (FiniteIntervals.merge match_part193 match_part194)) (FiniteIntervals.merge match_part195 (FiniteIntervals.merge match_part196 match_part197))) (FiniteIntervals.merge (FiniteIntervals.merge match_part198 (FiniteIntervals.merge match_part199 match_part200)) (FiniteIntervals.merge match_part201 (FiniteIntervals.merge match_part202 match_part203))))
#print axioms matches_interval16
end Erdos184Work.PureSevenActions
