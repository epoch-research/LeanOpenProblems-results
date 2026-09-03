import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_228 : Matches 228 := by decide +kernel
lemma match_part228 : FiniteIntervals.Covers MatchesAt 228 229 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 228 1
  intro i
  fin_cases i
  intro h
  exact matches_228
lemma matches_229 : Matches 229 := by decide +kernel
lemma match_part229 : FiniteIntervals.Covers MatchesAt 229 230 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 229 1
  intro i
  fin_cases i
  intro h
  exact matches_229
lemma matches_230 : Matches 230 := by decide +kernel
lemma match_part230 : FiniteIntervals.Covers MatchesAt 230 231 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 230 1
  intro i
  fin_cases i
  intro h
  exact matches_230
lemma matches_231 : Matches 231 := by decide +kernel
lemma match_part231 : FiniteIntervals.Covers MatchesAt 231 232 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 231 1
  intro i
  fin_cases i
  intro h
  exact matches_231
lemma matches_232 : Matches 232 := by decide +kernel
lemma match_part232 : FiniteIntervals.Covers MatchesAt 232 233 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 232 1
  intro i
  fin_cases i
  intro h
  exact matches_232
lemma matches_233 : Matches 233 := by decide +kernel
lemma match_part233 : FiniteIntervals.Covers MatchesAt 233 234 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 233 1
  intro i
  fin_cases i
  intro h
  exact matches_233
lemma matches_234 : Matches 234 := by decide +kernel
lemma match_part234 : FiniteIntervals.Covers MatchesAt 234 235 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 234 1
  intro i
  fin_cases i
  intro h
  exact matches_234
lemma matches_235 : Matches 235 := by decide +kernel
lemma match_part235 : FiniteIntervals.Covers MatchesAt 235 236 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 235 1
  intro i
  fin_cases i
  intro h
  exact matches_235
lemma matches_236 : Matches 236 := by decide +kernel
lemma match_part236 : FiniteIntervals.Covers MatchesAt 236 237 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 236 1
  intro i
  fin_cases i
  intro h
  exact matches_236
lemma matches_237 : Matches 237 := by decide +kernel
lemma match_part237 : FiniteIntervals.Covers MatchesAt 237 238 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 237 1
  intro i
  fin_cases i
  intro h
  exact matches_237
lemma matches_238 : Matches 238 := by decide +kernel
lemma match_part238 : FiniteIntervals.Covers MatchesAt 238 239 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 238 1
  intro i
  fin_cases i
  intro h
  exact matches_238
lemma matches_239 : Matches 239 := by decide +kernel
lemma match_part239 : FiniteIntervals.Covers MatchesAt 239 240 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 239 1
  intro i
  fin_cases i
  intro h
  exact matches_239
lemma matches_interval19 : FiniteIntervals.Covers MatchesAt 228 240 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part228 (FiniteIntervals.merge match_part229 match_part230)) (FiniteIntervals.merge match_part231 (FiniteIntervals.merge match_part232 match_part233))) (FiniteIntervals.merge (FiniteIntervals.merge match_part234 (FiniteIntervals.merge match_part235 match_part236)) (FiniteIntervals.merge match_part237 (FiniteIntervals.merge match_part238 match_part239))))
#print axioms matches_interval19
end Erdos184Work.PureSevenActions
