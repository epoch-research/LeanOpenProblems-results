import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_264 : Matches 264 := by decide +kernel
lemma match_part264 : FiniteIntervals.Covers MatchesAt 264 265 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 264 1
  intro i
  fin_cases i
  intro h
  exact matches_264
lemma matches_265 : Matches 265 := by decide +kernel
lemma match_part265 : FiniteIntervals.Covers MatchesAt 265 266 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 265 1
  intro i
  fin_cases i
  intro h
  exact matches_265
lemma matches_266 : Matches 266 := by decide +kernel
lemma match_part266 : FiniteIntervals.Covers MatchesAt 266 267 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 266 1
  intro i
  fin_cases i
  intro h
  exact matches_266
lemma matches_267 : Matches 267 := by decide +kernel
lemma match_part267 : FiniteIntervals.Covers MatchesAt 267 268 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 267 1
  intro i
  fin_cases i
  intro h
  exact matches_267
lemma matches_268 : Matches 268 := by decide +kernel
lemma match_part268 : FiniteIntervals.Covers MatchesAt 268 269 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 268 1
  intro i
  fin_cases i
  intro h
  exact matches_268
lemma matches_269 : Matches 269 := by decide +kernel
lemma match_part269 : FiniteIntervals.Covers MatchesAt 269 270 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 269 1
  intro i
  fin_cases i
  intro h
  exact matches_269
lemma matches_270 : Matches 270 := by decide +kernel
lemma match_part270 : FiniteIntervals.Covers MatchesAt 270 271 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 270 1
  intro i
  fin_cases i
  intro h
  exact matches_270
lemma matches_271 : Matches 271 := by decide +kernel
lemma match_part271 : FiniteIntervals.Covers MatchesAt 271 272 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 271 1
  intro i
  fin_cases i
  intro h
  exact matches_271
lemma matches_272 : Matches 272 := by decide +kernel
lemma match_part272 : FiniteIntervals.Covers MatchesAt 272 273 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 272 1
  intro i
  fin_cases i
  intro h
  exact matches_272
lemma matches_273 : Matches 273 := by decide +kernel
lemma match_part273 : FiniteIntervals.Covers MatchesAt 273 274 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 273 1
  intro i
  fin_cases i
  intro h
  exact matches_273
lemma matches_274 : Matches 274 := by decide +kernel
lemma match_part274 : FiniteIntervals.Covers MatchesAt 274 275 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 274 1
  intro i
  fin_cases i
  intro h
  exact matches_274
lemma matches_275 : Matches 275 := by decide +kernel
lemma match_part275 : FiniteIntervals.Covers MatchesAt 275 276 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 275 1
  intro i
  fin_cases i
  intro h
  exact matches_275
lemma matches_interval22 : FiniteIntervals.Covers MatchesAt 264 276 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part264 (FiniteIntervals.merge match_part265 match_part266)) (FiniteIntervals.merge match_part267 (FiniteIntervals.merge match_part268 match_part269))) (FiniteIntervals.merge (FiniteIntervals.merge match_part270 (FiniteIntervals.merge match_part271 match_part272)) (FiniteIntervals.merge match_part273 (FiniteIntervals.merge match_part274 match_part275))))
#print axioms matches_interval22
end Erdos184Work.PureSevenActions
