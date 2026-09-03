import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_240 : Matches 240 := by decide +kernel
lemma match_part240 : FiniteIntervals.Covers MatchesAt 240 241 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 240 1
  intro i
  fin_cases i
  intro h
  exact matches_240
lemma matches_241 : Matches 241 := by decide +kernel
lemma match_part241 : FiniteIntervals.Covers MatchesAt 241 242 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 241 1
  intro i
  fin_cases i
  intro h
  exact matches_241
lemma matches_242 : Matches 242 := by decide +kernel
lemma match_part242 : FiniteIntervals.Covers MatchesAt 242 243 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 242 1
  intro i
  fin_cases i
  intro h
  exact matches_242
lemma matches_243 : Matches 243 := by decide +kernel
lemma match_part243 : FiniteIntervals.Covers MatchesAt 243 244 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 243 1
  intro i
  fin_cases i
  intro h
  exact matches_243
lemma matches_244 : Matches 244 := by decide +kernel
lemma match_part244 : FiniteIntervals.Covers MatchesAt 244 245 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 244 1
  intro i
  fin_cases i
  intro h
  exact matches_244
lemma matches_245 : Matches 245 := by decide +kernel
lemma match_part245 : FiniteIntervals.Covers MatchesAt 245 246 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 245 1
  intro i
  fin_cases i
  intro h
  exact matches_245
lemma matches_246 : Matches 246 := by decide +kernel
lemma match_part246 : FiniteIntervals.Covers MatchesAt 246 247 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 246 1
  intro i
  fin_cases i
  intro h
  exact matches_246
lemma matches_247 : Matches 247 := by decide +kernel
lemma match_part247 : FiniteIntervals.Covers MatchesAt 247 248 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 247 1
  intro i
  fin_cases i
  intro h
  exact matches_247
lemma matches_248 : Matches 248 := by decide +kernel
lemma match_part248 : FiniteIntervals.Covers MatchesAt 248 249 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 248 1
  intro i
  fin_cases i
  intro h
  exact matches_248
lemma matches_249 : Matches 249 := by decide +kernel
lemma match_part249 : FiniteIntervals.Covers MatchesAt 249 250 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 249 1
  intro i
  fin_cases i
  intro h
  exact matches_249
lemma matches_250 : Matches 250 := by decide +kernel
lemma match_part250 : FiniteIntervals.Covers MatchesAt 250 251 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 250 1
  intro i
  fin_cases i
  intro h
  exact matches_250
lemma matches_251 : Matches 251 := by decide +kernel
lemma match_part251 : FiniteIntervals.Covers MatchesAt 251 252 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 251 1
  intro i
  fin_cases i
  intro h
  exact matches_251
lemma matches_interval20 : FiniteIntervals.Covers MatchesAt 240 252 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part240 (FiniteIntervals.merge match_part241 match_part242)) (FiniteIntervals.merge match_part243 (FiniteIntervals.merge match_part244 match_part245))) (FiniteIntervals.merge (FiniteIntervals.merge match_part246 (FiniteIntervals.merge match_part247 match_part248)) (FiniteIntervals.merge match_part249 (FiniteIntervals.merge match_part250 match_part251))))
#print axioms matches_interval20
end Erdos184Work.PureSevenActions
